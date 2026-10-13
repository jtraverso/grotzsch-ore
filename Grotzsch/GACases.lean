/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Grotzsch.GrunbaumAksenov

/-!
# Grünbaum–Aksenov: Cases 2 and 3, and the theorem

Continuation of `Grotzsch.GrunbaumAksenov`. Let `G` be a smallest counterexample (`GAMin G`) and
`M` a plane map of `G`; by Case 1 there is a four-face `F = v₀ v₁ v₂ v₃`.
* **Case 2** (`GAMin.not_adj_of_fourFace`): `F` has no chord. A chord `v₀ v₂` makes `v₀ v₁ v₂` a
  triangle; it does not separate `G` (`GAMin.rIn_of_clique`), so it is a face (`cycle_facial`),
  and together with `F` this forces `v₁` to have degree at most 2.
* **Lemma 10, first half** (`GAMin.exists_path_of_fourFace`): identifying `v₀` and `v₂` keeps the
  graph planar and smaller, so it must have more than three triangles; the new triangle comes from
  a path `v₀ p q v₂` with `p v₂` and `q v₀` not edges.
* **Crossing** (`no_crossing_paths_of_ne`): paths `v₀ p q v₂` and `v₁ p' q' v₃` with all eight
  vertices distinct cannot both exist (`K₅` minor with an apex inside `F`).
* **Case 3** (`GAMin.false`): the remaining configurations (BKLY Lemma 10 and Cases 3.1, 3.2).
-/

@[expose] public section

noncomputable section

open Classical Finset Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

namespace Grotzsch

variable {V : Type} [Fintype V] {G : SimpleGraph V}

/-! ### Case 2: four-faces have no chords -/

/-- **Case 2.** In a smallest counterexample, a four-face has no chord. -/
theorem GAMin.not_adj_of_fourFace (hG : GAMin G) (M : PlaneMap G) {d₀ d₁ d₂ d₃ : G.Dart}
    (hF : FourFace M d₀ d₁ d₂ d₃) : ¬ G.Adj d₀.fst d₂.fst := by
  sorry

/-! ### Crossing paths through a four-face -/

/-- Opposite corners of a vertex-injective 4-face `x y z u` cannot both be joined by paths of
length 3 whose interior vertices are off the face and distinct: the apex inside the face and the
two paths would form a `K₅` minor of a planar graph. -/
theorem no_crossing_paths_of_ne (M : PlaneMap G) (o : G.Dart)
    (hinj : ∀ e e' : FaceApex.F M o, e.1.fst = e'.1.fst → e = e') {x y z u : V}
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hzu : G.Adj z u) (hux : G.Adj u x) (hxz : x ≠ z)
    (hyu : y ≠ u)
    (hx : x ∈ FaceApex.faceVerts M o) (hy : y ∈ FaceApex.faceVerts M o)
    (hz : z ∈ FaceApex.faceVerts M o) (hu : u ∈ FaceApex.faceVerts M o)
    {b c b' c' : V} (hxb : G.Adj x b) (hbc : G.Adj b c) (hcz : G.Adj c z)
    (hyb' : G.Adj y b') (hb'c' : G.Adj b' c') (hc'u : G.Adj c' u)
    (hb : b ≠ x ∧ b ≠ y ∧ b ≠ z ∧ b ≠ u) (hc : c ≠ x ∧ c ≠ y ∧ c ≠ z ∧ c ≠ u)
    (hb' : b' ≠ x ∧ b' ≠ y ∧ b' ≠ z ∧ b' ≠ u) (hc' : c' ≠ x ∧ c' ≠ y ∧ c' ≠ z ∧ c' ≠ u)
    (hbb' : b ≠ b') (hbc' : b ≠ c') (hcb' : c ≠ b') (hcc' : c ≠ c') : False := by
  sorry

/-! ### Lemma 10, first half -/

/-- **Identification of opposite corners.** In a smallest counterexample, identifying the
opposite corners `v₀`, `v₂` of a four-face gives a smaller planar graph, so it has at least four
triangles; a triangle not coming from `G` is a path `v₀ p q v₂` with `p v₂` and `q v₀` not edges.
-/
theorem GAMin.exists_path_of_fourFace (hG : GAMin G) (M : PlaneMap G) {d₀ d₁ d₂ d₃ : G.Dart}
    (hF : FourFace M d₀ d₁ d₂ d₃) :
    ∃ p q, G.Adj d₀.fst p ∧ G.Adj p q ∧ G.Adj q d₂.fst ∧ ¬ G.Adj p d₂.fst ∧
      ¬ G.Adj q d₀.fst := by
  sorry

/-! ### Case 3 -/

/-- **Case 3.** There is no smallest counterexample. -/
theorem GAMin.false (hG : GAMin G) : False := by
  sorry

/-! ### The theorem -/

theorem grunbaum_aksenov_aux : ∀ (n : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V),
    Fintype.card V + Nat.card G.edgeSet = n → IsPlanar G → triCount G ≤ 3 → G.Colorable 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ G hn hP ht
  by_contra hc
  exact GAMin.false ⟨hP, ht, hc, fun W _ H hlt hP' ht' => ih _ (hn ▸ hlt) W H rfl hP' ht'⟩

/-- **Grünbaum–Aksenov theorem.** A planar graph with at most three triangles is
3-colourable. -/
theorem grunbaum_aksenov (G : SimpleGraph V) (hP : IsPlanar G) (ht : triCount G ≤ 3) :
    G.Colorable 3 :=
  grunbaum_aksenov_aux _ V G rfl hP ht

end Grotzsch
