/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Grotzsch.CycleExtension
public import Grotzsch.FacialCycle

/-!
# Grünbaum–Aksenov: planar graphs with at most three triangles are 3-colourable

**Theorem (Grünbaum 1963, Aksenov 1974, Borodin 1997; BKLY 2014, Theorem 7).** A planar graph
with at most three triangles is 3-colourable.

We follow Borodin–Kostochka–Lidický–Yancey (arXiv:1211.3981). This file sets up a smallest
counterexample `G` (`GAMin`) and proves the reductions used in the paper:
* `GAMin.isCritical4`: `G` is 4-critical, so `5|V| ≤ 3|E| + 2` (Kostochka–Yancey).
* `GAMin.rIn_of_clique`: a clique (e.g. a triangle) does not separate `G`; hence by
  `cycle_facial` every triangle is a face.
* `GAMin.sides`: if a 4- or 5-cycle separates `G`, both sides contain a triangle (otherwise
  colour one side by minimality and extend into the other by `exists_coloring_extend_four/five`).
* `GAMin.exists_four_face`: some face has length 4 (Case 1 of the paper: Euler's formula with at
  most three triangular faces contradicts Kostochka–Yancey).

"Separating" and "sides" are combinatorial: the two sides of a vertex set `S` are `S` together
with a component of `G - S`, and `S` together with the rest. No Jordan curve theorem is needed.
-/

@[expose] public section

noncomputable section

open Classical Finset Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

namespace Grotzsch

/-! ### Triangles -/

/-- The number of triangles of a graph. -/
def triCount {W : Type*} (H : SimpleGraph W) : ℕ := Nat.card {s : Finset W // H.IsNClique 3 s}

variable {V : Type} [Fintype V] {G : SimpleGraph V}

theorem triCount_le_of_injective {W : Type} [Fintype W] {X : SimpleGraph V} {Y : SimpleGraph W}
    (f : V → W) (hf : Function.Injective f) (hadj : ∀ a b, X.Adj a b → Y.Adj (f a) (f b)) :
    triCount X ≤ triCount Y := by
  let e : V ↪ W := ⟨f, hf⟩
  have hle : X.map e ≤ Y := by
    intro u v h
    obtain ⟨a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj e X u v).1 h
    exact hadj a b hab
  refine Nat.card_le_card_of_injective (fun s => ⟨s.1.map e, (s.2.map).mono hle⟩) ?_
  intro s t h
  exact Subtype.ext (Finset.map_injective e (congrArg Subtype.val h))

/-! ### A smallest counterexample -/

/-- Every planar graph with at most three triangles and fewer than `n` vertices plus edges is
3-colourable. -/
def GASmall (n : ℕ) : Prop :=
  ∀ (W : Type) [Fintype W] (H : SimpleGraph W), Fintype.card W + Nat.card H.edgeSet < n →
    IsPlanar H → triCount H ≤ 3 → H.Colorable 3

/-- A smallest counterexample to the Grünbaum–Aksenov theorem. -/
structure GAMin (G : SimpleGraph V) : Prop where
  planar : IsPlanar G
  tri : triCount G ≤ 3
  not_colorable : ¬ G.Colorable 3
  small : GASmall (Fintype.card V + Nat.card G.edgeSet)

theorem card_edgeSet_induce_le (H : SimpleGraph V) (s : Set V) :
    Nat.card (H.induce s).edgeSet ≤ Nat.card H.edgeSet := by
  refine Nat.card_le_card_of_injective
    (fun e => ⟨Sym2.map Subtype.val e.1, ?_⟩) fun e₁ e₂ h => ?_
  · obtain ⟨e, he⟩ := e
    induction e using Sym2.ind with
    | _ a b => simpa using he
  · exact Subtype.ext (Sym2.map.injective Subtype.val_injective (congrArg Subtype.val h))

/-- A smallest counterexample is 4-critical. -/
theorem GAMin.isCritical4 (hG : GAMin G) : IsCritical4 G := by
  refine ⟨hG.not_colorable, fun v => ?_, fun e he => ?_⟩
  · have hcard : Fintype.card {x | x ≠ v} < Fintype.card V :=
      Fintype.card_subtype_lt (p := fun x => x ≠ v) (x := v) (by simp)
    have hedge := card_edgeSet_induce_le G {x | x ≠ v}
    exact hG.small _ (G.induce {x | x ≠ v}) (by omega)
      (isPlanar_of_injective_hom' Subtype.val Subtype.val_injective (fun a b h => h) hG.planar)
      ((triCount_le_of_injective Subtype.val Subtype.val_injective fun a b h => h).trans hG.tri)
  · have hlt : Nat.card (G.deleteEdges {e}).edgeSet < Nat.card G.edgeSet := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
      refine LE.le.ssubset_of_ne
        (SimpleGraph.edgeSet_mono (G.deleteEdges_le _)) fun h => ?_
      have : e ∈ (G.deleteEdges {e}).edgeSet := by rw [h]; exact he
      simp at this
    have hadj : ∀ a b, (G.deleteEdges {e}).Adj a b → G.Adj (id a) (id b) :=
      fun a b h => (SimpleGraph.deleteEdges_adj.1 h).1
    exact hG.small V _ (by omega) (isPlanar_of_injective_hom' id Function.injective_id hadj
      hG.planar) ((triCount_le_of_injective id Function.injective_id hadj).trans hG.tri)

/-! ### Restrictions and gluing -/

omit [Fintype V] in
theorem restrict_adj_iff {s : Set V} {a b : V} :
    (restrict G s).Adj a b ↔ G.Adj a b ∧ a ∈ s ∧ b ∈ s := Iff.rfl

/-- Deleting all edges leaving `s` loses the edge `ab` if `a ∉ s`. -/
theorem card_edgeSet_restrict_lt {s : Set V} {a b : V} (hab : G.Adj a b) (ha : a ∉ s) :
    Nat.card (restrict G s).edgeSet < Nat.card G.edgeSet := by
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  refine Set.ncard_lt_ncard ⟨fun e he => ?_, fun h => ?_⟩ (Set.toFinite _)
  · induction e using Sym2.ind with
    | _ x y => exact (SimpleGraph.mem_edgeSet _).2 ((SimpleGraph.mem_edgeSet _).1 he).1
  · exact ha ((SimpleGraph.mem_edgeSet _).1 (h ((SimpleGraph.mem_edgeSet _).2 hab))).2.1

theorem isPlanar_restrict (hP : IsPlanar G) (s : Set V) : IsPlanar (restrict G s) :=
  isPlanar_of_injective_hom' (X := restrict G s) id Function.injective_id (fun _ _ h => h.1) hP

/-- Restrictions of a smallest counterexample with fewer edges are 3-colourable. -/
theorem GAMin.colorable_restrict (hG : GAMin G) {s : Set V}
    (hlt : Nat.card (restrict G s).edgeSet < Nat.card G.edgeSet) : (restrict G s).Colorable 3 :=
  hG.small V (restrict G s) (by omega)
    (isPlanar_restrict hG.planar s)
    ((triCount_le_of_injective (X := restrict G s) (Y := G) id Function.injective_id
      fun _ _ h => h.1).trans hG.tri)

omit [Fintype V] in
/-- **Gluing.** If every edge lies inside `A` or inside `B`, colourings of the two restrictions
that agree on `A ∩ B` combine. -/
theorem colorable_of_restrict_glue {A B : Set V}
    (hcross : ∀ a b, G.Adj a b → (a ∈ A ∧ b ∈ A) ∨ (a ∈ B ∧ b ∈ B))
    (f : (restrict G A).Coloring (Fin 3)) (g : (restrict G B).Coloring (Fin 3))
    (hfg : ∀ v ∈ A, v ∈ B → f v = g v) : G.Colorable 3 := by
  have key : ∀ v ∈ B, (if v ∈ A then f v else g v) = g v := fun v hv => by
    split_ifs with h
    · exact hfg v h hv
    · rfl
  refine ⟨SimpleGraph.Coloring.mk (fun v => if v ∈ A then f v else g v) fun {a b} hab => ?_⟩
  rcases hcross a b hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp only [ha, hb, ite_true]
    exact f.valid ⟨hab, ha, hb⟩
  · rw [key a ha, key b hb]
    exact g.valid ⟨hab, ha, hb⟩

/-! ### Separators -/

/-- The two sides of a separator `S` of a smallest counterexample: if `d.fst` and `e.fst` lie off
`S` and are not joined by a path avoiding `S`, then `V = A ∪ B` with `A ∩ B = S`, every edge inside
`A` or inside `B`, and both restrictions have fewer edges. -/
theorem exists_sides {S : Set V} {d e : G.Dart} (hd : d.fst ∉ S) (he : e.fst ∉ S)
    (hde : ¬ RIn G Sᶜ d.fst e.fst) :
    ∃ A B : Set V, S ⊆ A ∧ S ⊆ B ∧ (∀ v, v ∈ A → v ∈ B → v ∈ S) ∧
      (∀ a b, G.Adj a b → (a ∈ A ∧ b ∈ A) ∨ (a ∈ B ∧ b ∈ B)) ∧
      Nat.card (restrict G A).edgeSet < Nat.card G.edgeSet ∧
      Nat.card (restrict G B).edgeSet < Nat.card G.edgeSet := by
  set K : Set V := {w | w ∉ S ∧ RIn G Sᶜ d.fst w} with hK
  have hclose : ∀ w u, w ∈ K → G.Adj w u → u ∉ S → u ∈ K := fun w u hw hwu hu =>
    ⟨hu, Relation.ReflTransGen.tail hw.2 ⟨hwu, hw.1, hu⟩⟩
  refine ⟨S ∪ K, Kᶜ, Set.subset_union_left, fun s hs hsK => hsK.1 hs, ?_, ?_, ?_, ?_⟩
  · rintro v (hv | hv) hvK
    · exact hv
    · exact absurd hv hvK
  · intro a b hab
    by_cases ha : a ∈ K
    · left
      refine ⟨Or.inr ha, ?_⟩
      by_cases hb : b ∈ S
      · exact Or.inl hb
      · exact Or.inr (hclose a b ha hab hb)
    · by_cases hb : b ∈ K
      · left
        refine ⟨?_, Or.inr hb⟩
        by_contra haS
        rw [Set.mem_union, not_or] at haS
        exact ha (hclose b a hb hab.symm haS.1)
      · exact Or.inr ⟨ha, hb⟩
  · refine card_edgeSet_restrict_lt e.adj fun h => ?_
    rcases h with h | h
    · exact he h
    · exact hde h.2
  · exact card_edgeSet_restrict_lt d.adj fun h => h ⟨hd, Relation.ReflTransGen.refl⟩

/-- **A clique does not separate a smallest counterexample.** Colour both sides by minimality and
permute the colours of one side to match on the clique. -/
theorem GAMin.rIn_of_clique (hG : GAMin G) {S : Set V}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y) {d e : G.Dart} (hd : d.fst ∉ S)
    (he : e.fst ∉ S) : RIn G Sᶜ d.fst e.fst := by
  by_contra hde
  obtain ⟨A, B, hSA, hSB, hAB, hcross, hA, hB⟩ := exists_sides hd he hde
  obtain ⟨f⟩ := hG.colorable_restrict hA
  obtain ⟨g⟩ := hG.colorable_restrict hB
  have hpat : ∀ i j : S, g i = g j ↔ f i = f j := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      have hadj := hS i.1 i.2 j.1 j.2 hne
      exact ⟨fun h => absurd h (g.valid ⟨hadj, hSB i.2, hSB j.2⟩),
        fun h => absurd h (f.valid ⟨hadj, hSA i.2, hSA j.2⟩)⟩
  obtain ⟨π, hπ⟩ := exists_perm_of_pattern (fun i : S => g i) (fun i : S => f i) hpat
  exact hG.not_colorable (colorable_of_restrict_glue hcross f (recolour g π)
    fun v hvA hvB => (hπ ⟨v, hAB v hvA hvB⟩).symm)

/-- The precolouring-extension property of a vertex set `S` (true for 4- and 5-cycles). -/
def ExtProp (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ H : SimpleGraph V, IsPlanar H → H.CliqueFree 3 → (∀ x ∈ S, ∀ y ∈ S, G.Adj x y → H.Adj x y) →
    ∀ g : V → Fin 3, (∀ x ∈ S, ∀ y ∈ S, G.Adj x y → g x ≠ g y) →
      ∃ f : H.Coloring (Fin 3), ∀ x ∈ S, f x = g x

theorem extProp_four {c : ZMod 4 → V} (hinj : Function.Injective c)
    (hadj : ∀ i, G.Adj (c i) (c (i + 1))) : ExtProp G (Set.range c) := by
  intro H hP h3 hH g hg
  obtain ⟨f, hf⟩ := exists_coloring_extend_four hP h3 hinj
    (fun i => hH _ ⟨i, rfl⟩ _ ⟨i + 1, rfl⟩ (hadj i)) (fun i => g (c i))
    (fun i => hg _ ⟨i, rfl⟩ _ ⟨i + 1, rfl⟩ (hadj i))
  exact ⟨f, by rintro _ ⟨i, rfl⟩; exact hf i⟩

theorem extProp_five {c : ZMod 5 → V} (hadj : ∀ i, G.Adj (c i) (c (i + 1))) :
    ExtProp G (Set.range c) := by
  intro H hP h3 hH g hg
  obtain ⟨f, hf⟩ := exists_coloring_extend_five hP h3
    (fun i => hH _ ⟨i, rfl⟩ _ ⟨i + 1, rfl⟩ (hadj i)) (fun i => g (c i))
    (fun i => hg _ ⟨i, rfl⟩ _ ⟨i + 1, rfl⟩ (hadj i))
  exact ⟨f, by rintro _ ⟨i, rfl⟩; exact hf i⟩

/-- One side of a separator with the extension property contains a triangle, provided the other
side is coloured by minimality. -/
theorem GAMin.not_cliqueFree_of_extProp (hG : GAMin G) {S A B : Set V} (hext : ExtProp G S)
    (hSA : S ⊆ A) (hSB : S ⊆ B) (hAB : ∀ v, v ∈ A → v ∈ B → v ∈ S)
    (hcross : ∀ a b, G.Adj a b → (a ∈ A ∧ b ∈ A) ∨ (a ∈ B ∧ b ∈ B))
    (hB : Nat.card (restrict G B).edgeSet < Nat.card G.edgeSet) :
    ¬ (restrict G A).CliqueFree 3 := by
  intro h3
  obtain ⟨g⟩ := hG.colorable_restrict hB
  obtain ⟨f, hf⟩ := hext (restrict G A) (isPlanar_restrict hG.planar A) h3
    (fun x hx y hy hxy => ⟨hxy, hSA hx, hSA hy⟩) (fun v => g v)
    (fun x hx y hy hxy => g.valid ⟨hxy, hSB hx, hSB hy⟩)
  exact hG.not_colorable (colorable_of_restrict_glue hcross f g
    fun v hvA hvB => hf v (hAB v hvA hvB))

/-- **Both sides of a separating 4- or 5-cycle contain triangles.** -/
theorem GAMin.sides (hG : GAMin G) {S : Set V} (hext : ExtProp G S) {d e : G.Dart}
    (hd : d.fst ∉ S) (he : e.fst ∉ S) (hde : ¬ RIn G Sᶜ d.fst e.fst) :
    ∃ A B : Set V, S ⊆ A ∧ S ⊆ B ∧ (∀ v, v ∈ A → v ∈ B → v ∈ S) ∧
      (∀ a b, G.Adj a b → (a ∈ A ∧ b ∈ A) ∨ (a ∈ B ∧ b ∈ B)) ∧
      ¬ (restrict G A).CliqueFree 3 ∧ ¬ (restrict G B).CliqueFree 3 := by
  obtain ⟨A, B, hSA, hSB, hAB, hcross, hA, hB⟩ := exists_sides hd he hde
  refine ⟨A, B, hSA, hSB, hAB, hcross,
    hG.not_cliqueFree_of_extProp hext hSA hSB hAB hcross hB,
    hG.not_cliqueFree_of_extProp hext hSB hSA (fun v h1 h2 => hAB v h2 h1)
      (fun a b h => (hcross a b h).symm) hA⟩

/-! ### Case 1: some face has length four -/

/-- Counting classes with at most three exceptional classes of size three: if every class has at
least three elements, none has exactly four, and the classes of size three inject into a set of
at most three labels, then `5 · #classes ≤ |α| + 6`. -/
theorem five_mul_numClasses_le_add_six {α T : Type*} [Finite α] (s : Setoid α)
    (h3 : ∀ a, 3 ≤ Nat.card {b // s a b}) (h4 : ∀ a, Nat.card {b // s a b} ≠ 4)
    (τ : α → T) (R : Finset T) (hR : R.card ≤ 3)
    (hmem : ∀ a, Nat.card {b // s a b} = 3 → τ a ∈ R)
    (hτ : ∀ a a', Nat.card {b // s a b} = 3 → Nat.card {b // s a' b} = 3 → τ a = τ a' →
      s a a') :
    5 * numClasses s ≤ Nat.card α + 6 := by
  classical
  have := Fintype.ofFinite α
  have hsum := Finset.card_eq_sum_card_fiberwise
    (f := Quotient.mk s) (s := (Finset.univ : Finset α)) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  have hcard : ∀ a, (Finset.univ.filter fun b => Quotient.mk s b = Quotient.mk s a).card =
      Nat.card {b // s a b} := by
    intro a
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => s.symm (Quotient.exact h), fun h => Quotient.sound (s.symm h)⟩
  set Q3 : Finset (Quotient s) := Finset.univ.filter fun q =>
    (Finset.univ.filter fun a => Quotient.mk s a = q).card = 3 with hQ3def
  have hmemQ : ∀ a, Quotient.mk s a ∈ Q3 ↔ Nat.card {b // s a b} = 3 := fun a => by
    rw [hQ3def, Finset.mem_filter, hcard a]
    simp
  have hQ3 : Q3.card ≤ 3 := by
    refine le_trans (Finset.card_le_card_of_injOn (fun q => τ q.out) (fun q hq => ?_)
      fun q hq q' hq' h => ?_) hR
    · have hq2 : Quotient.mk s q.out ∈ Q3 := by rwa [Quotient.out_eq]
      exact hmem _ ((hmemQ _).1 hq2)
    · have hq2 : Quotient.mk s q.out ∈ Q3 := by rwa [Quotient.out_eq]
      have hq2' : Quotient.mk s q'.out ∈ Q3 := by rwa [Quotient.out_eq]
      have := hτ _ _ ((hmemQ _).1 hq2) ((hmemQ _).1 hq2') h
      rw [← Quotient.out_eq q, ← Quotient.out_eq q']
      exact Quotient.sound this
  have hfib : ∀ q : Quotient s, 5 ≤ (Finset.univ.filter fun a => Quotient.mk s a = q).card +
      (if q ∈ Q3 then 2 else 0) := by
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
    rw [hcard a]
    have := h3 a
    have := h4 a
    by_cases ha : Nat.card {b // s a b} = 3
    · rw [if_pos ((hmemQ a).2 ha)]; omega
    · split_ifs <;> omega
  have hle : ∑ q : Quotient s, 5 ≤ ∑ q : Quotient s,
      ((Finset.univ.filter fun a => Quotient.mk s a = q).card + (if q ∈ Q3 then 2 else 0)) :=
    Finset.sum_le_sum fun q _ => hfib q
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter] at hle
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
  simp only [numClasses, Nat.card_eq_fintype_card]
  rw [Finset.card_univ] at hsum
  rw [mul_comm]
  omega

omit [Fintype V] in
theorem card_adj_eq_degree (G : SimpleGraph V) (z : V) [Fintype (G.neighborSet z)] :
    Nat.card {w // G.Adj z w} = G.degree z := by
  rw [show Nat.card {w // G.Adj z w} = Nat.card (G.neighborSet z) from rfl,
    Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]

omit [Fintype V] in
theorem dart_eq_of {d e : G.Dart} (h1 : d.fst = e.fst) (h2 : d.snd = e.snd) : d = e :=
  (SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext h1 h2)

omit [Fintype V] in
@[simp] theorem dart_symm_fst (d : G.Dart) : d.symm.fst = d.snd := rfl

omit [Fintype V] in
@[simp] theorem dart_symm_snd (d : G.Dart) : d.symm.snd = d.fst := rfl

section Faces

variable (M : PlaneMap G)

theorem facePerm_fst' (d : G.Dart) : (M.facePerm d).fst = d.snd :=
  facePerm_fst M.isRotationSystem d

/-- In a plane map of minimum degree `≥ 2`, every face has at least three darts. -/
theorem three_le_card_face (hdeg : ∀ v, 2 ≤ Nat.card {u // G.Adj v u}) (d : G.Dart) :
    3 ≤ Nat.card {e // SameCycle M.facePerm d e} := by
  have ne1 : ∀ e, M.facePerm e ≠ e := fun e => face_ne_self M.isRotationSystem e
  have ne2 : ∀ e, M.facePerm (M.facePerm e) ≠ e :=
    fun e => face_face_ne_self M.isRotationSystem hdeg e
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hS : ({d, M.facePerm d, M.facePerm (M.facePerm d)} : Finset G.Dart).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [(ne1 d).symm, (ne2 d).symm]),
      Finset.card_insert_of_notMem (by simp [(ne1 _).symm]), Finset.card_singleton]
  rw [← hS]
  refine Finset.card_le_card fun e he => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases he with rfl | rfl | rfl
  · exact SameCycle.refl _ _
  · exact sameCycle_apply_right.2 (SameCycle.refl _ _)
  · exact sameCycle_apply_right.2 (sameCycle_apply_right.2 (SameCycle.refl _ _))

/-- A face with three darts closes up after three steps. -/
theorem facePerm_three_eq (hdeg : ∀ v, 2 ≤ Nat.card {u // G.Adj v u}) (d : G.Dart)
    (h : Nat.card {e // SameCycle M.facePerm d e} = 3) :
    M.facePerm (M.facePerm (M.facePerm d)) = d := by
  have ne1 : ∀ e, M.facePerm e ≠ e := fun e => face_ne_self M.isRotationSystem e
  have ne2 : ∀ e, M.facePerm (M.facePerm e) ≠ e :=
    fun e => face_face_ne_self M.isRotationSystem hdeg e
  set O := Finset.univ.filter fun e => SameCycle M.facePerm d e with hO
  have hOc : O.card = 3 := by rw [← h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hS : ({d, M.facePerm d, M.facePerm (M.facePerm d)} : Finset G.Dart).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [(ne1 d).symm, (ne2 d).symm]),
      Finset.card_insert_of_notMem (by simp [(ne1 _).symm]), Finset.card_singleton]
  have hSO : ({d, M.facePerm d, M.facePerm (M.facePerm d)} : Finset G.Dart) ⊆ O := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases he with rfl | rfl | rfl
    · exact SameCycle.refl _ _
    · exact sameCycle_apply_right.2 (SameCycle.refl _ _)
    · exact sameCycle_apply_right.2 (sameCycle_apply_right.2 (SameCycle.refl _ _))
  have hEq := Finset.eq_of_subset_of_card_le hSO (by omega)
  have hmem : M.facePerm (M.facePerm (M.facePerm d)) ∈ O := by
    simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and]
    exact sameCycle_apply_right.2 (sameCycle_apply_right.2 (sameCycle_apply_right.2
      (SameCycle.refl _ _)))
  rw [← hEq] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h1 | h1
  · exact h1
  · exact absurd (M.facePerm.injective h1) (ne2 d)
  · exact absurd h1 (ne1 _)

/-- The vertex set of the face through `d`, read off its first two darts. -/
def faceTri (d : G.Dart) : Finset V := {d.fst, d.snd, (M.facePerm d).snd}

theorem faceTri_isNClique (d : G.Dart) (h3 : M.facePerm (M.facePerm (M.facePerm d)) = d) :
    G.IsNClique 3 (faceTri M d) := by
  have e1 := facePerm_fst' M d
  have e2 := facePerm_fst' M (M.facePerm d)
  have e3 := facePerm_fst' M (M.facePerm (M.facePerm d))
  rw [h3] at e3
  have a1 : G.Adj d.fst d.snd := d.adj
  have a2 : G.Adj d.snd (M.facePerm d).snd := e1 ▸ (M.facePerm d).adj
  have a3 : G.Adj (M.facePerm d).snd d.fst := by
    have := (M.facePerm (M.facePerm d)).adj
    rwa [e2, ← e3] at this
  exact SimpleGraph.is3Clique_triple_iff.2 ⟨a1, a3.symm, a2⟩

theorem faceTri_facePerm (d : G.Dart) (h3 : M.facePerm (M.facePerm (M.facePerm d)) = d) :
    faceTri M (M.facePerm d) = faceTri M d := by
  have e1 := facePerm_fst' M d
  have e2 := facePerm_fst' M (M.facePerm d)
  have e3 := facePerm_fst' M (M.facePerm (M.facePerm d))
  rw [h3] at e3
  simp only [faceTri, e1, ← e2, e3]
  ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

/-- A triangular face is not traversed in both directions when all degrees are `≥ 3`. -/
theorem faceTri_rev_false (hdeg : ∀ v, 3 ≤ Nat.card {u // G.Adj v u}) {b a' : G.Dart}
    (hb : M.facePerm (M.facePerm (M.facePerm b)) = b) (ha' : a' = b.symm)
    (hτ : faceTri M a' = faceTri M b) : False := by
  have e1 := facePerm_fst' M b
  have e2 := facePerm_fst' M (M.facePerm b)
  have e3 := facePerm_fst' M (M.facePerm (M.facePerm b))
  rw [hb] at e3
  have hyz : b.snd ≠ (M.facePerm b).snd := by rw [← e1]; exact (M.facePerm b).adj.ne
  have hzx : (M.facePerm b).snd ≠ b.fst := by
    have := (M.facePerm (M.facePerm b)).adj.ne
    rwa [e2, ← e3] at this
  have hfa : (M.facePerm a').fst = b.fst := by rw [facePerm_fst', ha']; rfl
  have hzmem : (M.facePerm b).snd ∈ faceTri M a' := by rw [hτ]; simp [faceTri]
  have hsnd : (M.facePerm a').snd = (M.facePerm b).snd := by
    simp only [faceTri, ha', dart_symm_fst, dart_symm_snd,
      Finset.mem_insert, Finset.mem_singleton] at hzmem
    rcases hzmem with h | h | h
    · exact absurd h hyz.symm
    · exact absurd h hzx
    · rw [ha']; exact h.symm
  have r1 : M.rot b = M.facePerm a' := by
    rw [PlaneMap.facePerm_apply, ha', SimpleGraph.Dart.symm_symm]
  have r2 : M.rot (M.facePerm a') = b := by
    have : (M.facePerm (M.facePerm b)).symm = M.facePerm a' :=
      dart_eq_of (by rw [dart_symm_fst, hfa, ← e3])
        (by rw [dart_symm_snd, e2, hsnd])
    rw [← this, ← PlaneMap.facePerm_apply, hb]
  have := card_adj_le_two_of_rot_swap M r1 r2
  have := hdeg b.fst
  omega

/-- Two triangular faces with the same vertices are the same face. -/
theorem sameCycle_of_faceTri_eq (hdeg : ∀ v, 3 ≤ Nat.card {u // G.Adj v u}) {a a' : G.Dart}
    (ha : M.facePerm (M.facePerm (M.facePerm a)) = a)
    (hτ : faceTri M a' = faceTri M a) : SameCycle M.facePerm a a' := by
  have e1 := facePerm_fst' M a
  have e2 := facePerm_fst' M (M.facePerm a)
  have e3 := facePerm_fst' M (M.facePerm (M.facePerm a))
  rw [ha] at e3
  have ha1 : M.facePerm (M.facePerm (M.facePerm (M.facePerm a))) = M.facePerm a := by rw [ha]
  have ha2 : M.facePerm (M.facePerm (M.facePerm (M.facePerm (M.facePerm a)))) =
      M.facePerm (M.facePerm a) := by rw [ha]
  have t1 := faceTri_facePerm M a ha
  have t2 : faceTri M (M.facePerm (M.facePerm a)) = faceTri M a :=
    (faceTri_facePerm M _ ha1).trans t1
  have s1 : SameCycle M.facePerm a (M.facePerm a) :=
    sameCycle_apply_right.2 (SameCycle.refl _ _)
  have s2 : SameCycle M.facePerm a (M.facePerm (M.facePerm a)) := sameCycle_apply_right.2 s1
  have hf : a'.fst ∈ faceTri M a := by rw [← hτ]; simp [faceTri]
  have hs : a'.snd ∈ faceTri M a := by rw [← hτ]; simp [faceTri]
  simp only [faceTri, Finset.mem_insert, Finset.mem_singleton] at hf hs
  have hne := a'.adj.ne
  rcases hf with hf | hf | hf <;> rcases hs with hs | hs | hs
  · exact absurd (hf.trans hs.symm) hne
  · rw [dart_eq_of hf hs]
  · exact (faceTri_rev_false M hdeg (b := M.facePerm (M.facePerm a)) (a' := a') ha2
      (dart_eq_of (by rw [hf, dart_symm_fst, e3])
        (by rw [hs, dart_symm_snd, e2])) (hτ.trans t2.symm)).elim
  · exact (faceTri_rev_false M hdeg (b := a) (a' := a') ha
      (dart_eq_of (by rw [hf]; rfl) (by rw [hs]; rfl)) hτ).elim
  · exact absurd (hf.trans hs.symm) hne
  · have : a' = M.facePerm a := dart_eq_of (by rw [hf, e1]) hs
    rw [this]; exact s1
  · have : a' = M.facePerm (M.facePerm a) := dart_eq_of (by rw [hf, e2]) (by rw [hs, e3])
    rw [this]; exact s2
  · exact (faceTri_rev_false M hdeg (b := M.facePerm a) (a' := a') ha1
      (dart_eq_of (by rw [hf, dart_symm_fst])
        (by rw [hs, dart_symm_snd, e1])) (hτ.trans t1.symm)).elim
  · exact absurd (hf.trans hs.symm) hne

end Faces

/-- **Case 1 of the paper.** A smallest counterexample has a face of length 4: otherwise every
face has length at least 5 except at most three triangular faces, and Euler's formula gives
`3|E| ≤ 5|V| - 4`, contradicting `5|V| ≤ 3|E| + 2`. -/
theorem GAMin.exists_four_face (hG : GAMin G) (M : PlaneMap G) :
    ∃ d : G.Dart, Nat.card {e // SameCycle M.facePerm d e} = 4 := by
  by_contra h4
  push Not at h4
  have hcrit := hG.isCritical4
  have hore := five_mul_card_le G hcrit
  rw [card_edgeFinset_eq_natCard] at hore
  have hdeg : ∀ v, 3 ≤ Nat.card {u // G.Adj v u} := fun v => by
    rw [card_adj_eq_degree]; exact hcrit.three_le_degree v
  have hdeg2 : ∀ v, 2 ≤ Nat.card {u // G.Adj v u} := fun v => by have := hdeg v; omega
  have hiso : ∀ v, ∃ u, G.Adj v u := fun v => by
    obtain ⟨⟨u, hu⟩⟩ := (Nat.card_pos_iff (α := {u // G.Adj v u}).mp
      (by have := hdeg v; omega)).1
    exact ⟨u, hu⟩
  have hdart : Nonempty G.Dart := by
    obtain ⟨v⟩ : Nonempty V := by
      by_contra hV
      rw [not_nonempty_iff] at hV
      exact hG.not_colorable ⟨SimpleGraph.Coloring.mk (fun v => isEmptyElim v)
        fun {v} => isEmptyElim v⟩
    obtain ⟨u, hu⟩ := hiso v
    exact ⟨⟨(v, u), hu⟩⟩
  have hR : (Finset.univ.filter fun t : Finset V => G.IsNClique 3 t).card ≤ 3 := by
    have := hG.tri
    rwa [triCount, Nat.card_eq_fintype_card, Fintype.card_subtype] at this
  have hφ : 5 * cycleCount (M.rot * dartSymm G) ≤ Nat.card G.Dart + 6 :=
    five_mul_numClasses_le_add_six (SameCycle.setoid M.facePerm)
      (fun d => three_le_card_face M hdeg2 d) h4 (faceTri M) _ hR
      (fun d hd => Finset.mem_filter.2 ⟨Finset.mem_univ _,
        faceTri_isNClique M d (facePerm_three_eq M hdeg2 d hd)⟩)
      (fun a a' ha _ hτ => sameCycle_of_faceTri_eq M hdeg
        (facePerm_three_eq M hdeg2 a ha) hτ.symm)
  have h0 := M.eulerDefect_eq_zero
  have hα := card_dart_eq_two_mul G
  have hE := card_edgeSet_eq_cycleCount (G := G)
  have hK := one_le_numComponents M.rot (dartSymm G)
  have hn := cycleCount_eq_card_nonisolated M.isRotationSystem
  have hn' : Nat.card {v // ∃ u, G.Adj v u} = Fintype.card V := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hiso), Nat.card_eq_fintype_card]
  unfold eulerDefect at h0
  omega

end Grotzsch
