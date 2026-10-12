/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Grotzsch.Ore
public import LeanPool.K5MinorFreeChoosability.Planar.Nonplanar
public import LeanPool.K5MinorFreeChoosability.Planar.FaceApex
public import LeanPool.K5MinorFreeChoosability.Planar.MinorClosed
public import LeanPool.K5MinorFreeChoosability.Planar.Examples
public import LeanPool.K5MinorFreeChoosability.Frontier.PlanarDensity
public import LeanPool.K5MinorFreeChoosability.Frontier.ApexTools
public import LeanPool.K5MinorFreeChoosability.Wagner.WagnerA

/-!
# Grötzsch's theorem

**Theorem (Grötzsch 1959).** Every finite triangle-free planar graph is 3-colourable.

Planarity is the combinatorial notion `IsPlanar` of the `K5MinorFreeChoosability` library: the
existence of a genus-zero rotation system (`PlaneMap`). We follow the short proof of
Kostochka–Yancey (Combinatorica 2014, §3), which deduces Grötzsch's theorem from their bound
`3|E| ≥ 5|V| - 2` for 4-critical graphs (`Grotzsch.five_mul_card_le`):

Let `G` be a counterexample with the fewest vertices plus edges. It is 4-critical.
* If every face has length `≥ 5`, Euler's formula gives `3|E| ≤ 5|V| - 10`, contradicting the
  bound.
* Otherwise there is a face `x y z u` of length 4. Identifying `x` with `z` (`glue`) keeps the
  graph planar (it is a minor of `G` plus an apex inside the face) and smaller, so it must
  contain a triangle, i.e. `G` has a path `x b c z`. Likewise `G` has a path `y b' c' u`.
  The apex inside the face together with these two paths forms a `K₅` minor in a planar graph,
  which is impossible (`cliqueMinorFree_five_of_isPlanar`). This replaces the topological
  "crossing paths" argument of the paper.
-/

@[expose] public section

noncomputable section

open Classical Finset Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

namespace Grotzsch

variable {V : Type} [Fintype V] {G : SimpleGraph V}

/-- The number of edges, independently of the `Fintype` instance on the edge set. -/
theorem card_edgeFinset_eq_natCard (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeFinset.card = Nat.card G.edgeSet := by
  rw [SimpleGraph.edgeFinset, Set.toFinset_card, Nat.card_eq_fintype_card]

/-! ### Face counting -/

/-- If every face of a plane map has at least five darts and there are no isolated vertices,
then `3|E| + 10 ≤ 5|V|`. -/
theorem three_mul_card_edgeFinset_add_ten_le (M : PlaneMap G) [Nonempty G.Dart]
    (hiso : ∀ v, ∃ u, G.Adj v u)
    (h5 : ∀ d : G.Dart, 5 ≤ Nat.card {e // SameCycle M.facePerm d e}) :
    3 * G.edgeFinset.card + 10 ≤ 5 * Fintype.card V := by
  sorry

/-- A face with at most four darts in a triangle-free plane graph of minimum degree `≥ 2` is a
4-cycle `x y z u` on four distinct vertices, and the face is vertex-injective. -/
theorem exists_four_face (M : PlaneMap G) (h3 : G.CliqueFree 3) (hmin : ∀ v, 2 ≤ G.degree v)
    (d : G.Dart) (hd : Nat.card {e // SameCycle M.facePerm d e} ≤ 4) :
    ∃ x y z u : V, G.Adj x y ∧ G.Adj y z ∧ G.Adj z u ∧ G.Adj u x ∧ x ≠ z ∧ y ≠ u ∧
      (∀ e e' : FaceApex.F M d, e.1.fst = e'.1.fst → e = e') ∧
      x ∈ FaceApex.faceVerts M d ∧ y ∈ FaceApex.faceVerts M d ∧
      z ∈ FaceApex.faceVerts M d ∧ u ∈ FaceApex.faceVerts M d := by
  sorry

/-! ### Identifying two vertices -/

/-- The graph obtained from `G` by identifying `z` into `x` (vertex set `V \ {z}`). -/
def glue (G : SimpleGraph V) (x z : V) : SimpleGraph {v // v ≠ z} where
  Adj a b := a ≠ b ∧ (G.Adj a b ∨ (a.1 = x ∧ G.Adj z b) ∨ (b.1 = x ∧ G.Adj z a))
  symm := ⟨fun a b h => ⟨h.1.symm, by
    rcases h.2 with h' | h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr (Or.inr h')
    · exact Or.inr (Or.inl h')⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

/-- Identifying two vertices `x`, `z` of a vertex-injective face keeps the graph planar: it is a
minor of `G` with an apex added inside the face. -/
theorem isPlanar_glue (M : PlaneMap G) (o : G.Dart)
    (hinj : ∀ e e' : FaceApex.F M o, e.1.fst = e'.1.fst → e = e') {x z : V} (hxz : x ≠ z)
    (hx : x ∈ FaceApex.faceVerts M o) (hz : z ∈ FaceApex.faceVerts M o) :
    IsPlanar (glue G x z) := by
  sorry

/-- A 3-colouring of the identified graph gives a 3-colouring of `G` (if `x z` is not an edge). -/
theorem colorable_of_glue {x z : V} (hxz : x ≠ z) (hadj : ¬ G.Adj x z)
    (h : (glue G x z).Colorable 3) : G.Colorable 3 := by
  obtain ⟨C⟩ := h
  have hzx : ∀ b, G.Adj z b → b ≠ x := fun b hb hbx => hadj (hbx ▸ hb).symm
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => if hv : v = z then C ⟨x, hxz⟩ else C ⟨v, hv⟩) fun {a b} hab => ?_⟩
  by_cases ha : a = z <;> by_cases hb : b = z
  · subst ha; subst hb; exact absurd hab (G.loopless.irrefl _)
  · subst ha
    simp only [dite_eq_right_iff, dif_neg hb]
    refine C.valid ⟨fun h => hzx b hab (congrArg Subtype.val h).symm, Or.inr (Or.inl ⟨rfl, hab⟩)⟩
  · subst hb
    simp only [dif_neg ha]
    refine C.valid ⟨fun h => hzx a hab.symm (congrArg Subtype.val h), Or.inr (Or.inr ⟨rfl, hab.symm⟩)⟩
  · simp only [dif_neg ha, dif_neg hb]
    exact C.valid ⟨fun h => hab.ne (congrArg Subtype.val h), Or.inl hab⟩

/-- If identifying `x` and `z` (non-adjacent, at distance 2 via `y` and `u`) creates a triangle in
a triangle-free graph, there is a path `x b c z` avoiding `y` and `u`. -/
theorem exists_path_of_not_cliqueFree_glue (h3 : G.CliqueFree 3) {x z : V} (hxz : x ≠ z)
    (hadj : ¬ G.Adj x z) (h : ¬ (glue G x z).CliqueFree 3) :
    ∃ b c, G.Adj x b ∧ G.Adj b c ∧ G.Adj c z ∧ b ≠ z ∧ c ≠ x := by
  have tri : ∀ p q r : V, G.Adj p q → G.Adj p r → G.Adj q r → False := fun p q r hpq hpr hqr =>
    h3 {p, q, r} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hpq, hpr, hqr⟩)
  simp only [SimpleGraph.CliqueFree, not_forall, not_not] at h
  obtain ⟨t, ht⟩ := h
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.mp ht
  -- the adjacency of `glue` between two vertices different from `x` is that of `G`
  have plain : ∀ p q : {v // v ≠ z}, p.1 ≠ x → q.1 ≠ x → (glue G x z).Adj p q → G.Adj p q :=
    fun p q hp hq hpq => by
      rcases hpq.2 with h' | h' | h'
      · exact h'
      · exact absurd h'.1 hp
      · exact absurd h'.1 hq
  -- adjacency of `glue` from `x` to a vertex `q ≠ x`
  have fromx : ∀ p q : {v // v ≠ z}, p.1 = x → q.1 ≠ x → (glue G x z).Adj p q →
      G.Adj x q ∨ G.Adj z q := fun p q hp hq hpq => by
    rcases hpq.2 with h' | h' | h'
    · exact Or.inl (hp ▸ h')
    · exact Or.inr h'.2
    · exact absurd h'.1 hq
  -- the main case: `p = x`, `q`, `r` the other two
  have main : ∀ p q r : {v // v ≠ z}, p.1 = x → q.1 ≠ x → r.1 ≠ x →
      (glue G x z).Adj p q → (glue G x z).Adj p r → (glue G x z).Adj q r →
      ∃ b c, G.Adj x b ∧ G.Adj b c ∧ G.Adj c z ∧ b ≠ z ∧ c ≠ x := by
    intro p q r hp hq hr hpq hpr hqr
    have hqr' := plain q r hq hr hqr
    rcases fromx p q hp hq hpq with h1 | h1 <;> rcases fromx p r hp hr hpr with h2 | h2
    · exact (tri x q r h1 h2 hqr').elim
    · exact ⟨q, r, h1, hqr', h2.symm, q.2, hr⟩
    · exact ⟨r, q, h2, hqr'.symm, h1.symm, r.2, hq⟩
    · exact (tri z q r h1 h2 hqr').elim
  by_cases ha : a.1 = x
  · have hb : b.1 ≠ x := fun h => hab.1 (Subtype.ext (ha.trans h.symm))
    have hc : c.1 ≠ x := fun h => hac.1 (Subtype.ext (ha.trans h.symm))
    exact main a b c ha hb hc hab hac hbc
  by_cases hb : b.1 = x
  · have hc : c.1 ≠ x := fun h => hbc.1 (Subtype.ext (hb.trans h.symm))
    exact main b a c hb ha hc hab.symm hbc hac
  by_cases hc : c.1 = x
  · exact main c a b hc ha hb hac.symm hbc.symm hab
  exact (tri a b c (plain a b ha hb hab) (plain a c ha hc hac) (plain b c hb hc hbc)).elim

/-- Identifying two vertices does not increase the number of edges. -/
theorem card_edgeSet_glue_le (x z : V) (hxz : x ≠ z) :
    Nat.card (glue G x z).edgeSet ≤ Nat.card G.edgeSet := by
  sorry

/-! ### No two crossing paths through a face -/

/-- In a planar graph, the opposite vertices of a vertex-injective 4-face `x y z u` cannot both be
joined by paths of length 3 in a triangle-free graph: the apex inside the face and the two paths
would form a `K₅` minor. -/
theorem no_crossing_paths (M : PlaneMap G) (o : G.Dart) (h3 : G.CliqueFree 3)
    (hinj : ∀ e e' : FaceApex.F M o, e.1.fst = e'.1.fst → e = e') {x y z u : V}
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hzu : G.Adj z u) (hux : G.Adj u x)
    (hx : x ∈ FaceApex.faceVerts M o) (hy : y ∈ FaceApex.faceVerts M o)
    (hz : z ∈ FaceApex.faceVerts M o) (hu : u ∈ FaceApex.faceVerts M o)
    {b c b' c' : V} (hxb : G.Adj x b) (hbc : G.Adj b c) (hcz : G.Adj c z)
    (hyb' : G.Adj y b') (hb'c' : G.Adj b' c') (hc'u : G.Adj c' u) : False := by
  sorry

/-! ### Grötzsch's theorem -/

/-- **Grötzsch's theorem.** Every finite triangle-free planar graph is 3-colourable. -/
theorem grotzsch_aux : ∀ (n : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V),
    Fintype.card V + Nat.card G.edgeSet = n → IsPlanar G → G.CliqueFree 3 → G.Colorable 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ G hn hP h3
  by_contra hcol
  have tri : ∀ p q r : V, G.Adj p q → G.Adj p r → G.Adj q r → False := fun p q r hpq hpr hqr =>
    h3 {p, q, r} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hpq, hpr, hqr⟩)
  -- `G` is 4-critical
  have hcrit : IsCritical4 G := by
    refine ⟨hcol, fun v => ?_, fun e he => ?_⟩
    · have hcard : Fintype.card {w | w ≠ v} < Fintype.card V :=
        Fintype.card_subtype_lt (p := fun w => w ≠ v) (x := v) (by simp)
      have hedge : Nat.card (G.induce {w | w ≠ v}).edgeSet ≤ Nat.card G.edgeSet := by
        refine Nat.card_le_card_of_injective
          (fun e => ⟨Sym2.map Subtype.val e.1, ?_⟩) fun e₁ e₂ h => ?_
        · obtain ⟨e, he⟩ := e
          induction e using Sym2.ind with
          | _ a b => simpa using he
        · exact Subtype.ext (Sym2.map.injective Subtype.val_injective (congrArg Subtype.val h))
      exact ih _ (by omega) _ (G.induce {w | w ≠ v}) rfl
        (isPlanar_of_injective_hom Subtype.val Subtype.val_injective (fun a b h => h) hP)
        (h3.comap (SimpleGraph.Embedding.induce _).isContained)
    · have hlt : Nat.card (G.deleteEdges {e}).edgeSet < Nat.card G.edgeSet := by
        rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
        refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
        refine HasSubset.Subset.ssubset_of_ne
          (SimpleGraph.edgeSet_mono (G.deleteEdges_le _)) fun h => ?_
        have : e ∈ (G.deleteEdges {e}).edgeSet := by rw [h]; exact he
        simp at this
      exact ih _ (by omega) V (G.deleteEdges {e}) rfl (hP.mono (G.deleteEdges_le _))
        (h3.anti (G.deleteEdges_le _))
  have hore := five_mul_card_le G hcrit
  rw [card_edgeFinset_eq_natCard] at hore
  have hmin := hcrit.three_le_degree
  have hne : Nonempty V := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hcol (SimpleGraph.Colorable.of_isEmpty 3)
  have hiso : ∀ v, ∃ u, G.Adj v u := by
    intro v
    have := hmin v
    obtain ⟨u, hu⟩ := Finset.card_pos.mp
      (by rw [G.card_neighborFinset_eq_degree]; omega : 0 < (G.neighborFinset v).card)
    exact ⟨u, (G.mem_neighborFinset v u).mp hu⟩
  have hdart : Nonempty G.Dart := by
    obtain ⟨v⟩ := hne
    obtain ⟨u, hu⟩ := hiso v
    exact ⟨⟨(v, u), hu⟩⟩
  obtain ⟨M⟩ := hP
  by_cases hall : ∀ d : G.Dart, 5 ≤ Nat.card {e // SameCycle M.facePerm d e}
  · have := three_mul_card_edgeFinset_add_ten_le M hiso hall
    rw [card_edgeFinset_eq_natCard] at this
    omega
  push Not at hall
  obtain ⟨d, hd⟩ := hall
  obtain ⟨x, y, z, u, hxy, hyz, hzu, hux, hxz, hyu, hinj, hx, hy, hz, hu⟩ :=
    exists_four_face M h3 (fun v => by have := hmin v; omega) d (by omega)
  have hadjxz : ¬ G.Adj x z := fun h => tri x y z hxy h hyz
  have hadjyu : ¬ G.Adj y u := fun h => tri y z u hyz h hzu
  -- identifying two opposite vertices of the face must create a triangle
  have key : ∀ a c, a ≠ c → ¬ G.Adj a c → a ∈ FaceApex.faceVerts M d →
      c ∈ FaceApex.faceVerts M d → ¬ (glue G a c).CliqueFree 3 := by
    intro a c hac hadj ha hc hcf
    have hcard : Fintype.card {v // v ≠ c} < Fintype.card V :=
      Fintype.card_subtype_lt (p := fun w => w ≠ c) (x := c) (by simp)
    have hedge := card_edgeSet_glue_le (G := G) a c hac
    exact hcol (colorable_of_glue hac hadj (ih _ (by omega) _ (glue G a c) rfl
      (isPlanar_glue M d hinj hac ha hc) hcf))
  obtain ⟨b, c, hxb, hbc, hcz, -, -⟩ :=
    exists_path_of_not_cliqueFree_glue h3 hxz hadjxz (key x z hxz hadjxz hx hz)
  obtain ⟨b', c', hyb', hb'c', hc'u, -, -⟩ :=
    exists_path_of_not_cliqueFree_glue h3 hyu hadjyu (key y u hyu hadjyu hy hu)
  exact no_crossing_paths M d h3 hinj hxy hyz hzu hux hx hy hz hu hxb hbc hcz hyb' hb'c' hc'u

theorem grotzsch (G : SimpleGraph V) (hP : IsPlanar G) (h3 : G.CliqueFree 3) : G.Colorable 3 :=
  grotzsch_aux _ V G rfl hP h3

end Grotzsch
