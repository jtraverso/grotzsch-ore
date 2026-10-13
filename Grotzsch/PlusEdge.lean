/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Grotzsch.PlusVertex

/-!
# A triangle-free planar graph plus one edge is 3-colourable

**Theorem (Aksenov 1974; Jensen–Thomassen 2000; BKLY 2014, Theorem 2).** If `G` is a
triangle-free planar graph and `H` is obtained from `G` by adding one edge, then `H` is
3-colourable.

We follow Borodin–Kostochka–Lidický–Yancey (arXiv:1211.3981). Let `H = G + uv` be a counterexample
with the fewest vertices plus edges; it is 4-critical, so `3|E(H)| ≥ 5|V(H)| - 2`.
* **Case 1**: at most one face of `G` has length 4. Euler's formula gives `3|E(H)| ≤ 5|V| - 6`.
* **Case 2**: every 4-face has `u, v` as opposite corners and there are two of them,
  `u x₁ v x₂` and `u y₁ v y₂`. The `x`'s and `y`'s are distinct (a common one would be a vertex
  of degree 2, as the two faces would traverse the same path in opposite directions).
  Identifying `x₁` with `x₂` keeps `G` triangle-free: otherwise a path `x₁ q₁ q₂ x₂` exists, and
  it must contain `y₁` and `y₂` (`path_through_common_neighbour`, a `K₅`-minor argument with an
  apex inside the face), so `y₁ y₂` is an edge and `u y₁ y₂` a triangle.
* **Case 3**: some 4-face does not have `u, v` as opposite corners. One of the two identifications
  of opposite corners keeps `G` triangle-free (`no_crossing_paths`), and it maps `uv` to an edge.
In cases 2 and 3 the identified graph is again of the form (triangle-free planar) + one edge and
is smaller, hence 3-colourable, and so is `H`.

The topological "crossing" claims of the paper are replaced by `K₅`-minor arguments.
-/

@[expose] public section

noncomputable section

open Classical Finset Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

namespace Grotzsch

variable {V : Type} [Fintype V] {G : SimpleGraph V}

/-! ### Four-faces with explicit darts -/

/-- A face of length four, with its darts `d₀ → d₁ → d₂ → d₃ → d₀` and four distinct corners. -/
structure FourFace (M : PlaneMap G) (d₀ d₁ d₂ d₃ : G.Dart) : Prop where
  f01 : M.facePerm d₀ = d₁
  f12 : M.facePerm d₁ = d₂
  f23 : M.facePerm d₂ = d₃
  f30 : M.facePerm d₃ = d₀
  cover : ∀ e, SameCycle M.facePerm d₀ e → e = d₀ ∨ e = d₁ ∨ e = d₂ ∨ e = d₃
  ne02 : d₀.fst ≠ d₂.fst
  ne13 : d₁.fst ≠ d₃.fst

/-- A face with at most four darts in a triangle-free plane graph of minimum degree `≥ 2` is a
four-face. -/
theorem exists_fourFace (M : PlaneMap G) (h3 : G.CliqueFree 3) (hmin : ∀ v, 2 ≤ G.degree v)
    (d : G.Dart) (hd : Nat.card {e // SameCycle M.facePerm d e} ≤ 4) :
    ∃ d₁ d₂ d₃, FourFace M d d₁ d₂ d₃ := by
  sorry

namespace FourFace

variable {M : PlaneMap G} {d₀ d₁ d₂ d₃ : G.Dart}

theorem snd₀ (h : FourFace M d₀ d₁ d₂ d₃) : d₀.snd = d₁.fst := by
  sorry
theorem snd₁ (h : FourFace M d₀ d₁ d₂ d₃) : d₁.snd = d₂.fst := by
  sorry
theorem snd₂ (h : FourFace M d₀ d₁ d₂ d₃) : d₂.snd = d₃.fst := by
  sorry
theorem snd₃ (h : FourFace M d₀ d₁ d₂ d₃) : d₃.snd = d₀.fst := by
  sorry

/-- The face is vertex-injective. -/
theorem inj (h : FourFace M d₀ d₁ d₂ d₃) :
    ∀ e e' : FaceApex.F M d₀, e.1.fst = e'.1.fst → e = e' := by
  sorry

/-- The corners lie on the face. -/
theorem mem_faceVerts (h : FourFace M d₀ d₁ d₂ d₃) :
    d₀.fst ∈ FaceApex.faceVerts M d₀ ∧ d₁.fst ∈ FaceApex.faceVerts M d₀ ∧
      d₂.fst ∈ FaceApex.faceVerts M d₀ ∧ d₃.fst ∈ FaceApex.faceVerts M d₀ := by
  sorry

/-- Rotating the labels of a four-face gives a four-face (with the same face). -/
theorem rotate (h : FourFace M d₀ d₁ d₂ d₃) : FourFace M d₁ d₂ d₃ d₀ := by
  sorry

end FourFace

/-! ### Degree-two vertices from the rotation -/

/-- If the rotation swaps two distinct darts at a vertex, the vertex has at most two
neighbours. -/
theorem card_adj_le_two_of_rot_swap (M : PlaneMap G) {e₁ e₂ : G.Dart}
    (h12 : M.rot e₁ = e₂) (h21 : M.rot e₂ = e₁) : Nat.card {u // G.Adj e₁.fst u} ≤ 2 := by
  sorry

/-- Two faces traversing the path `u z v` in opposite directions force `z` to have degree at
most two. -/
theorem card_adj_le_two_of_opposite (M : PlaneMap G) {u z v : V} (huz : G.Adj u z)
    (hzv : G.Adj z v)
    (h1 : M.facePerm ⟨(u, z), huz⟩ = ⟨(z, v), hzv⟩)
    (h2 : M.facePerm ⟨(v, z), hzv.symm⟩ = ⟨(z, u), huz.symm⟩) :
    Nat.card {w // G.Adj z w} ≤ 2 := by
  sorry

/-! ### Euler's formula with one exceptional face -/

/-- If every face has at least four darts and all but at most one have at least five, and there
are no isolated vertices, then `3|E| + 9 ≤ 5|V|`. -/
theorem three_mul_card_edgeSet_add_nine_le (M : PlaneMap G) [Nonempty G.Dart]
    (hiso : ∀ v, ∃ u, G.Adj v u)
    (h4 : ∀ d : G.Dart, 4 ≤ Nat.card {e // SameCycle M.facePerm d e})
    (h5 : ∀ d d' : G.Dart, Nat.card {e // SameCycle M.facePerm d e} = 4 →
      Nat.card {e // SameCycle M.facePerm d' e} = 4 → SameCycle M.facePerm d d') :
    3 * Nat.card G.edgeSet + 9 ≤ 5 * Fintype.card V := by
  sorry

/-! ### Paths across a face must pass through every other common neighbour -/

/-- Let `u x₁ v x₂` be the corners of a vertex-injective face, and `y` another common neighbour of
`u` and `v`. A path `x₁ q₁ q₂ x₂` avoiding `u`, `v` passes through `y`: otherwise the apex inside
the face, `{u, y}`, `{v}`, `{x₁, q₁, q₂}` and `{x₂}` would form a `K₅` minor of a planar graph. -/
theorem path_through_common_neighbour (M : PlaneMap G) (o : G.Dart)
    (hinj : ∀ e e' : FaceApex.F M o, e.1.fst = e'.1.fst → e = e')
    {u x₁ v x₂ y q₁ q₂ : V}
    (hu : u ∈ FaceApex.faceVerts M o) (hx₁ : x₁ ∈ FaceApex.faceVerts M o)
    (hv : v ∈ FaceApex.faceVerts M o) (hx₂ : x₂ ∈ FaceApex.faceVerts M o)
    (hux₁ : G.Adj u x₁) (hux₂ : G.Adj u x₂) (hvx₁ : G.Adj v x₁) (hvx₂ : G.Adj v x₂)
    (huy : G.Adj u y) (hvy : G.Adj v y)
    (hx₁q₁ : G.Adj x₁ q₁) (hq₁q₂ : G.Adj q₁ q₂) (hq₂x₂ : G.Adj q₂ x₂)
    (hy : y ≠ x₁ ∧ y ≠ x₂ ∧ y ≠ q₁ ∧ y ≠ q₂)
    (hq : q₁ ≠ u ∧ q₁ ≠ v ∧ q₂ ≠ u ∧ q₂ ≠ v) (hxx : x₁ ≠ x₂) (huv : u ≠ v) : False := by
  sorry

/-! ### The theorem -/

/-- **BKLY, Theorem 2** (auxiliary form). -/
theorem colorable_of_sdiff_edge_aux : ∀ (n : ℕ) (V : Type) [Fintype V] (H : SimpleGraph V)
    (u v : V), Fintype.card V + Nat.card H.edgeSet = n → u ≠ v →
    IsPlanar (H.deleteEdges {s(u, v)}) → (H.deleteEdges {s(u, v)}).CliqueFree 3 →
    H.Colorable 3 := by
  sorry

/-- **Aksenov / Jensen–Thomassen.** A graph obtained from a triangle-free planar graph by adding one
edge is 3-colourable. -/
theorem colorable_of_sdiff_edge (H : SimpleGraph V) {u v : V} (huv : u ≠ v)
    (hP : IsPlanar (H.deleteEdges {s(u, v)})) (h3 : (H.deleteEdges {s(u, v)}).CliqueFree 3) :
    H.Colorable 3 :=
  colorable_of_sdiff_edge_aux _ V H u v rfl huv hP h3

end Grotzsch
