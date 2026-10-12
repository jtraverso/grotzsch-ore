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
  sorry

/-- If identifying `x` and `z` (non-adjacent, at distance 2 via `y` and `u`) creates a triangle in
a triangle-free graph, there is a path `x b c z` avoiding `y` and `u`. -/
theorem exists_path_of_not_cliqueFree_glue (h3 : G.CliqueFree 3) {x z : V} (hxz : x ≠ z)
    (hadj : ¬ G.Adj x z) (h : ¬ (glue G x z).CliqueFree 3) :
    ∃ b c, G.Adj x b ∧ G.Adj b c ∧ G.Adj c z ∧ b ≠ z ∧ c ≠ x := by
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
    Fintype.card V + G.edgeFinset.card = n → IsPlanar G → G.CliqueFree 3 → G.Colorable 3 := by
  sorry

theorem grotzsch (G : SimpleGraph V) (hP : IsPlanar G) (h3 : G.CliqueFree 3) : G.Colorable 3 :=
  grotzsch_aux _ V G rfl hP h3

end Grotzsch
