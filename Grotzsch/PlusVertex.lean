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
  sorry

/-- The number of edges of `H` is at most that of `H - v` plus the degree of `v`. -/
theorem natCard_edgeSet_le_induce_add_degree {V : Type} [Fintype V] (H : SimpleGraph V) (v : V) :
    Nat.card H.edgeSet ≤ Nat.card (H.induce {w | w ≠ v}).edgeSet + H.degree v := by
  sorry

/-- Deleting a vertex lowers every other degree by at most one. -/
theorem degree_induce_ne_add_one {V : Type} [Fintype V] (H : SimpleGraph V) (v : V)
    (w : {x // x ≠ v}) : H.degree w.1 ≤ (H.induce {x | x ≠ v}).degree w + 1 := by
  sorry

/-! ### The theorem -/

/-- **BKLY, Theorem 4** (auxiliary form, by induction on vertices plus edges). -/
theorem colorable_of_induce_planar_cliqueFree_aux : ∀ (n : ℕ) (V : Type) [Fintype V]
    (H : SimpleGraph V) (v : V), Fintype.card V + Nat.card H.edgeSet = n →
    IsPlanar (H.induce {w | w ≠ v}) → (H.induce {w | w ≠ v}).CliqueFree 3 → H.degree v ≤ 4 →
    H.Colorable 3 := by
  sorry

/-- **Borodin–Kostochka–Lidický–Yancey, Theorem 4.** A graph obtained from a triangle-free planar
graph by adding a vertex of degree at most four is 3-colourable. -/
theorem colorable_of_induce_planar_cliqueFree {V : Type} [Fintype V] (H : SimpleGraph V) (v : V)
    (hP : IsPlanar (H.induce {w | w ≠ v})) (h3 : (H.induce {w | w ≠ v}).CliqueFree 3)
    (hv : H.degree v ≤ 4) : H.Colorable 3 :=
  colorable_of_induce_planar_cliqueFree_aux _ V H v rfl hP h3 hv

end Grotzsch
