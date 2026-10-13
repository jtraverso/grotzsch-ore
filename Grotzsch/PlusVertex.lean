/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Grotzsch.Planar

/-!
# A triangle-free planar graph plus a vertex of degree at most four is 3-colourable

**Theorem (Borodin–Kostochka–Lidický–Yancey 2014, Theorem 4).** Let `H` be a graph and `v` a
vertex of degree at most `4` such that `H - v` is planar and triangle-free. Then `H` is
3-colourable. (The case of degree `3` is due to Jensen and Thomassen.)

Reference: O. V. Borodin, A. V. Kostochka, B. Lidický, M. Yancey, *Short proofs of coloring
theorems on planar graphs*, European J. Combin. 36 (2014) 314–321, arXiv:1211.3981.

Proof. Let `H` be a counterexample with the fewest vertices plus edges; it is 4-critical, so
`3|E(H)| ≥ 5|V(H)| - 2` (Kostochka–Yancey). Let `G = H - v`: it has `n - 1` vertices, at least
`|E(H)| - 4` edges, and minimum degree `≥ 2`.
* If every face of a plane map of `G` has length `≥ 5`, Euler's formula gives
  `3|E(G)| + 10 ≤ 5(n - 1)`, hence `3|E(H)| ≤ 5n - 3`: contradiction.
* Otherwise `G` has a 4-face `x y z u` (`exists_four_face`). Identifying `x, z` or `y, u` in `G`
  keeps it triangle-free for at least one of the two pairs (`no_crossing_paths`). Identifying
  the same pair in `H` gives a smaller graph of the same kind (the identified graph minus `v` is
  the identified `G`, planar by `isPlanar_glue`, and `v` still has degree `≤ 4`), hence
  3-colourable by minimality, and so is `H` (`colorable_of_glue`): contradiction.
-/

@[expose] public section

noncomputable section

open Classical Finset Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

namespace Grotzsch

/-! ### Transport along injective homomorphisms -/

/-- Planarity and triangle-freeness pass to graphs with an injective adjacency-preserving map
into a graph with these properties. -/
theorem planar_cliqueFree_of_injective {A B : Type} [Fintype A] [Fintype B]
    {X : SimpleGraph A} {Y : SimpleGraph B} (f : A → B) (hf : Function.Injective f)
    (hadj : ∀ a b, X.Adj a b → Y.Adj (f a) (f b)) :
    (IsPlanar Y → IsPlanar X) ∧ (Y.CliqueFree 3 → X.CliqueFree 3) := by
  refine ⟨isPlanar_of_injective_hom' f hf hadj, fun h => ?_⟩
  let c : SimpleGraph.Copy X Y := ⟨⟨f, fun {a b} hab => hadj a b hab⟩, hf⟩
  exact h.comap ⟨c⟩

/-- The number of edges of `H` is at most that of `H - v` plus the degree of `v`. -/
theorem natCard_edgeSet_le_induce_add_degree {V : Type} [Fintype V] (H : SimpleGraph V) (v : V) :
    Nat.card H.edgeSet ≤ Nat.card (H.induce {w | w ≠ v}).edgeSet + H.degree v := by
  have hpre : ∀ e : H.edgeSet, ∃ x : (H.induce {w | w ≠ v}).edgeSet ⊕ H.neighborSet v,
      Sum.elim (fun e' => Sym2.map Subtype.val e'.1) (fun w => s(v, w.1)) x = e.1 := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b =>
    have hab : H.Adj a b := he
    by_cases ha : a = v
    · subst ha
      exact ⟨Sum.inr ⟨b, hab⟩, rfl⟩
    by_cases hb : b = v
    · subst hb
      exact ⟨Sum.inr ⟨a, hab.symm⟩, Sym2.eq_swap⟩
    · exact ⟨Sum.inl ⟨s(⟨a, ha⟩, ⟨b, hb⟩), hab⟩, rfl⟩
  choose g hg using hpre
  have hinj : Function.Injective g := fun e₁ e₂ h =>
    Subtype.ext ((hg e₁).symm.trans (h ▸ hg e₂))
  have h1 := Nat.card_le_card_of_injective g hinj
  rw [Nat.card_sum, Nat.card_eq_fintype_card (α := H.neighborSet v),
    SimpleGraph.card_neighborSet_eq_degree] at h1
  exact h1

/-- Deleting a vertex lowers every other degree by at most one. -/
theorem degree_induce_ne_add_one {V : Type} [Fintype V] (H : SimpleGraph V) (v : V)
    (w : {x // x ≠ v}) : H.degree w.1 ≤ (H.induce {x | x ≠ v}).degree w + 1 := by
  rw [← H.card_neighborFinset_eq_degree, ← (H.induce _).card_neighborFinset_eq_degree]
  have hsub : H.neighborFinset w.1 ⊆ insert v
      (((H.induce {x | x ≠ v}).neighborFinset w).map (Function.Embedding.subtype _)) := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    by_cases hyv : y = v
    · simp [hyv]
    · apply Finset.mem_insert_of_mem
      simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset]
      exact ⟨⟨y, hyv⟩, hy, rfl⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_insert_le _ _
    _ = _ := by rw [Finset.card_map]

/-! ### Auxiliary lemmas -/

private lemma pv_degree_le_of_inj {A B : Type} (X : SimpleGraph A)
    (Y : SimpleGraph B) (a : A) (b : B) {_ : Fintype (X.neighborSet a)}
    {_ : Fintype (Y.neighborSet b)} (f : A → B) (hf : ∀ w, X.Adj a w → Y.Adj b (f w))
    (hinj : ∀ w₁ w₂, X.Adj a w₁ → X.Adj a w₂ → f w₁ = f w₂ → w₁ = w₂) :
    X.degree a ≤ Y.degree b := by
  rw [← X.card_neighborFinset_eq_degree, ← Y.card_neighborFinset_eq_degree]
  refine Finset.card_le_card_of_injOn f (fun w hw => ?_) (fun w₁ hw₁ w₂ hw₂ h => ?_)
  · simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw ⊢
    exact hf w hw
  · simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw₁ hw₂
    exact hinj w₁ w₂ hw₁ hw₂ h

private lemma pv_card_edgeSet_induce_le {V : Type} [Fintype V] (H : SimpleGraph V) (s : Set V) :
    Nat.card (H.induce s).edgeSet ≤ Nat.card H.edgeSet := by
  refine Nat.card_le_card_of_injective
    (fun e => ⟨Sym2.map Subtype.val e.1, ?_⟩) fun e₁ e₂ h => ?_
  · obtain ⟨e, he⟩ := e
    induction e using Sym2.ind with
    | _ a b => simpa using he
  · exact Subtype.ext (Sym2.map.injective Subtype.val_injective (congrArg Subtype.val h))

/-! ### The theorem -/

/-- **BKLY, Theorem 4** (auxiliary form, by induction on vertices plus edges). -/
theorem colorable_of_induce_planar_cliqueFree_aux : ∀ (n : ℕ) (V : Type) [Fintype V]
    (H : SimpleGraph V) (v : V), Fintype.card V + Nat.card H.edgeSet = n →
    IsPlanar (H.induce {w | w ≠ v}) → (H.induce {w | w ≠ v}).CliqueFree 3 → H.degree v ≤ 4 →
    H.Colorable 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ H v hn hP h3 hv
  by_contra hcol
  have tri : ∀ p q r : {w | w ≠ v}, (H.induce {w | w ≠ v}).Adj p q →
      (H.induce {w | w ≠ v}).Adj p r → (H.induce {w | w ≠ v}).Adj q r → False :=
    fun p q r hpq hpr hqr =>
      h3 {p, q, r} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hpq, hpr, hqr⟩)
  -- `H` is 4-critical
  have hcrit : IsCritical4 H := by
    refine ⟨hcol, fun w => ?_, fun e he => ?_⟩
    · by_cases hwv : w = v
      · subst hwv
        exact grotzsch _ hP h3
      have hvw : v ≠ w := Ne.symm hwv
      have hcard : Fintype.card {x | x ≠ w} < Fintype.card V :=
        Fintype.card_subtype_lt (p := fun x => x ≠ w) (x := w) (by simp)
      have hedge := pv_card_edgeSet_induce_le H {x | x ≠ w}
      have hT := planar_cliqueFree_of_injective
        (X := (H.induce {x | x ≠ w}).induce {y | y ≠ (⟨v, hvw⟩ : {x | x ≠ w})})
        (Y := H.induce {x | x ≠ v})
        (fun y => ⟨y.1.1, fun h => y.2 (Subtype.ext h)⟩)
        (fun y₁ y₂ h => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h)))
        (fun a b h => h)
      exact ih _ (by omega) _ (H.induce {x | x ≠ w}) ⟨v, hvw⟩ rfl (hT.1 hP) (hT.2 h3)
        ((pv_degree_le_of_inj _ H _ v Subtype.val (fun y h => h)
          (fun y₁ y₂ _ _ h => Subtype.ext h)).trans hv)
    · have hlt : Nat.card (H.deleteEdges {e}).edgeSet < Nat.card H.edgeSet := by
        rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
        refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
        refine LE.le.ssubset_of_ne
          (SimpleGraph.edgeSet_mono (H.deleteEdges_le _)) fun h => ?_
        have : e ∈ (H.deleteEdges {e}).edgeSet := by rw [h]; exact he
        simp at this
      have hT := planar_cliqueFree_of_injective
        (X := (H.deleteEdges {e}).induce {w | w ≠ v}) (Y := H.induce {w | w ≠ v})
        id Function.injective_id (fun a b h => (H.deleteEdges_le _) h)
      exact ih _ (by omega) V (H.deleteEdges {e}) v rfl (hT.1 hP) (hT.2 h3)
        ((pv_degree_le_of_inj _ H v v id (fun y h => (H.deleteEdges_le _) h)
          (fun _ _ _ _ h => h)).trans hv)
  have hore := five_mul_card_le H hcrit
  rw [card_edgeFinset_eq_natCard] at hore
  have hmin := hcrit.three_le_degree
  have hminG : ∀ w : {x | x ≠ v}, 2 ≤ (H.induce {x | x ≠ v}).degree w := fun w => by
    have h1 := hmin w.1
    have h2 := degree_induce_ne_add_one H v w
    omega
  have hiso : ∀ w : {x | x ≠ v}, ∃ u, (H.induce {x | x ≠ v}).Adj w u := by
    intro w
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by
      rw [(H.induce {x | x ≠ v}).card_neighborFinset_eq_degree]
      have := hminG w
      omega : 0 < ((H.induce {x | x ≠ v}).neighborFinset w).card)
    exact ⟨u, ((H.induce {x | x ≠ v}).mem_neighborFinset w u).mp hu⟩
  have hdart : Nonempty (H.induce {x | x ≠ v}).Dart := by
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by
      rw [H.card_neighborFinset_eq_degree]
      have := hmin v
      omega : 0 < (H.neighborFinset v).card)
    have hu' : H.Adj v u := (H.mem_neighborFinset v u).mp hu
    obtain ⟨u', hu''⟩ := hiso ⟨u, hu'.ne.symm⟩
    exact ⟨⟨(_, u'), hu''⟩⟩
  have hcardG : Fintype.card {x | x ≠ v} < Fintype.card V :=
    Fintype.card_subtype_lt (p := fun x => x ≠ v) (x := v) (by simp)
  have hEH := natCard_edgeSet_le_induce_add_degree H v
  obtain ⟨M⟩ := hP
  by_cases hall : ∀ d : (H.induce {x | x ≠ v}).Dart,
      5 ≤ Nat.card {e // SameCycle M.facePerm d e}
  · have := three_mul_card_edgeSet_add_ten_le M hiso hall
    omega
  push Not at hall
  obtain ⟨d, hd⟩ := hall
  obtain ⟨x, y, z, u, hxy, hyz, hzu, hux, hxz, hyu, hinj, hx, hy, hz, hu⟩ :=
    exists_four_face M h3 (fun w => hminG w) d (by omega)
  have hadjxz : ¬ (H.induce {x | x ≠ v}).Adj x z := fun h => tri x y z hxy h hyz
  have hadjyu : ¬ (H.induce {x | x ≠ v}).Adj y u := fun h => tri y z u hyz h hzu
  -- identifying two opposite vertices of the face must create a triangle
  have key : ∀ a c : {x | x ≠ v}, a ≠ c → ¬ (H.induce {x | x ≠ v}).Adj a c →
      a ∈ FaceApex.faceVerts M d → c ∈ FaceApex.faceVerts M d →
      ¬ (glue (H.induce {x | x ≠ v}) a c).CliqueFree 3 := by
    intro a c hac hadj ha hc hcf
    have hac' : a.1 ≠ c.1 := fun h => hac (Subtype.ext h)
    have hadj' : ¬ H.Adj a.1 c.1 := hadj
    have hvc : v ≠ c.1 := fun h => c.2 h.symm
    have hcard : Fintype.card {w // w ≠ c.1} < Fintype.card V :=
      Fintype.card_subtype_lt (p := fun w => w ≠ c.1) (x := c.1) (by simp)
    have hedge := card_edgeSet_glue_le (G := H) a.1 c.1 hac'
    have hT := planar_cliqueFree_of_injective
      (X := (glue H a.1 c.1).induce {w | w ≠ (⟨v, hvc⟩ : {w // w ≠ c.1})})
      (Y := glue (H.induce {x | x ≠ v}) a c)
      (fun y => ⟨⟨y.1.1, fun h => y.2 (Subtype.ext h)⟩,
        fun h => y.1.2 (congrArg Subtype.val h)⟩)
      (fun y₁ y₂ h => Subtype.ext (Subtype.ext (congrArg (fun t => t.1.1) h)))
      (fun y₁ y₂ h => by
        obtain ⟨hne, h⟩ := h
        refine ⟨fun e => hne (Subtype.ext (congrArg (fun t => t.1.1) e)), ?_⟩
        rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨Subtype.ext h1, h2⟩)
        · exact Or.inr (Or.inr ⟨Subtype.ext h1, h2⟩))
    have hglue : ∀ w : {w // w ≠ c.1}, (glue H a.1 c.1).Adj ⟨v, hvc⟩ w →
        H.Adj v w.1 ∨ (w.1 = a.1 ∧ H.Adj c.1 v) := by
      intro w h
      rcases h.2 with h | ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact Or.inl h
      · exact absurd h1.symm a.2
      · exact Or.inr ⟨h1, h2⟩
    have hdeg : (glue H a.1 c.1).degree ⟨v, hvc⟩ ≤ H.degree v := by
      refine pv_degree_le_of_inj _ H _ v (fun w => if H.Adj v w.1 then w.1 else c.1)
        (fun w h => ?_) (fun w₁ w₂ h₁ h₂ h => ?_)
      · by_cases hw : H.Adj v w.1
        · simp only [hw, ↓reduceIte]
        · simp only [hw, ↓reduceIte]
          rcases hglue w h with h' | ⟨-, h'⟩
          · exact absurd h' hw
          · exact h'.symm
      · by_cases hw₁ : H.Adj v w₁.1 <;> by_cases hw₂ : H.Adj v w₂.1 <;>
          simp only [hw₁, hw₂, ↓reduceIte] at h
        · exact Subtype.ext h
        · exact absurd h w₁.2
        · exact absurd h.symm w₂.2
        · rcases hglue w₁ h₁ with h' | ⟨e₁, -⟩
          · exact absurd h' hw₁
          rcases hglue w₂ h₂ with h' | ⟨e₂, -⟩
          · exact absurd h' hw₂
          exact Subtype.ext (e₁.trans e₂.symm)
    exact hcol (colorable_of_glue hac' hadj' (ih _ (by omega) _ (glue H a.1 c.1) ⟨v, hvc⟩ rfl
      (hT.1 (isPlanar_glue M d hinj hac ha hc)) (hT.2 hcf) (hdeg.trans hv)))
  obtain ⟨b, c, hxb, hbc, hcz, -, -⟩ :=
    exists_path_of_not_cliqueFree_glue h3 hxz hadjxz (key x z hxz hadjxz hx hz)
  obtain ⟨b', c', hyb', hb'c', hc'u, -, -⟩ :=
    exists_path_of_not_cliqueFree_glue h3 hyu hadjyu (key y u hyu hadjyu hy hu)
  exact no_crossing_paths M d h3 hinj hxy hyz hzu hux hx hy hz hu hxb hbc hcz hyb' hb'c' hc'u

/-- **Borodin–Kostochka–Lidický–Yancey, Theorem 4.** A graph obtained from a triangle-free planar
graph by adding a vertex of degree at most four is 3-colourable. -/
theorem colorable_of_induce_planar_cliqueFree {V : Type} [Fintype V] (H : SimpleGraph V) (v : V)
    (hP : IsPlanar (H.induce {w | w ≠ v})) (h3 : (H.induce {w | w ≠ v}).CliqueFree 3)
    (hv : H.degree v ≤ 4) : H.Colorable 3 :=
  colorable_of_induce_planar_cliqueFree_aux _ V H v rfl hP h3 hv

end Grotzsch
