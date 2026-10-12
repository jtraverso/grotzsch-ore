/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Option
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

/-!
# Ore's conjecture for `k = 4` (Kostochka–Yancey)

**Theorem (Kostochka–Yancey 2014).** Every 4-critical graph `G` satisfies
`3 |E(G)| ≥ 5 |V(G)| - 2`.

Reference: A. Kostochka, M. Yancey, *Ore's conjecture for k = 4 and Grötzsch's theorem*,
Combinatorica 34 (2014) 323–329, arXiv:1209.1173.

The proof uses the *potential* `ρ_G(R) = 5|R| - 3 e(G[R])` and considers a vertex-minimal
4-critical graph `G` with `ρ_G(V) > 2` (`MinCounter`). Minimality gives (3): every graph with fewer
vertices all of whose nonempty vertex sets have potential `> 2` is 3-colourable
(`SmallColorable`). Claims 9–13 of the paper restrict the local structure of `G`, and a
discharging argument then gives `3 |E| ≥ 5 |V|`, a contradiction.
-/

@[expose] public section

noncomputable section

open Classical Finset

namespace Grotzsch

/-- Number of edges of `G` with both ends in `R`. -/
def eIn {V : Type*} [Fintype V] (G : SimpleGraph V) (R : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ R).card

/-- The potential `ρ_G(R) = 5 |R| - 3 e(G[R])`. -/
def pot {V : Type*} [Fintype V] (G : SimpleGraph V) (R : Finset V) : ℤ :=
  5 * (R.card : ℤ) - 3 * (eIn G R : ℤ)

/-- `G` is 4-critical: not 3-colourable, but deleting any vertex or any edge makes it
3-colourable. -/
structure IsCritical4 {V : Type*} (G : SimpleGraph V) : Prop where
  not_colorable : ¬ G.Colorable 3
  vertex : ∀ v, (G.induce {w | w ≠ v}).Colorable 3
  edge : ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).Colorable 3

/-- Hypothesis (3) of Kostochka–Yancey: every graph on fewer than `N` vertices whose nonempty
vertex sets all have potential `> 2` is 3-colourable. -/
def SmallColorable (N : ℕ) : Prop :=
  ∀ (W : Type) [Fintype W] (H : SimpleGraph W), Fintype.card W < N →
    (∀ R : Finset W, R.Nonempty → 2 < pot H R) → H.Colorable 3

/-- A minimal counterexample to the Kostochka–Yancey bound. -/
structure MinCounter {V : Type} [Fintype V] (G : SimpleGraph V) : Prop where
  crit : IsCritical4 G
  big : 2 < pot G univ
  small : SmallColorable (Fintype.card V)

/-! ### General facts -/

/-- Every finite graph that is not 3-colourable contains a 4-critical subgraph (on a subset of
the vertices). -/
theorem exists_critical_subgraph {W : Type} [Fintype W] (H : SimpleGraph W)
    (h : ¬ H.Colorable 3) :
    ∃ (S : Finset W) (H' : SimpleGraph S), (∀ a b, H'.Adj a b → H.Adj a b) ∧ IsCritical4 H' := by
  sorry

/-- In a 4-critical graph every vertex has degree at least 3. -/
theorem IsCritical4.three_le_degree {V : Type} [Fintype V] {G : SimpleGraph V}
    (h : IsCritical4 G) (v : V) : 3 ≤ G.degree v := by
  sorry

/-- Minimality of the counterexample gives hypothesis (3). -/
theorem smallColorable_of_minimal (N : ℕ)
    (ih : ∀ (W : Type) [Fintype W] (H : SimpleGraph W), Fintype.card W < N →
      IsCritical4 H → pot H univ ≤ 2) :
    SmallColorable N := by
  sorry

/-! ### Claims 9–13 for a minimal counterexample -/

section Claims

variable {V : Type} [Fintype V] {G : SimpleGraph V}

/-- **Claim 9.** Every proper subset `R` with `|R| ≥ 2` has potential at least `6`. -/
theorem MinCounter.claim9 (hG : MinCounter G) (R : Finset V) (hR : R ≠ univ)
    (h2 : 2 ≤ R.card) : 6 ≤ pot G R := by
  sorry

/-- **Claim 10.** A proper subset `R` with `|R| ≥ 2` and potential `≤ 6` spans a triangle. -/
theorem MinCounter.claim10 (hG : MinCounter G) (R : Finset V) (hR : R ≠ univ)
    (h2 : 2 ≤ R.card) (h6 : pot G R ≤ 6) : R.card = 3 ∧ eIn G R = 3 := by
  sorry

/-- **Claim 11.** `G` contains no `K₄ - e`: four vertices span at most four edges. -/
theorem MinCounter.claim11 (hG : MinCounter G) (R : Finset V) (h4 : R.card = 4) :
    eIn G R ≤ 4 := by
  sorry

/-- **Claim 12.** Each triangle contains at most one vertex of degree 3. -/
theorem MinCounter.claim12 (hG : MinCounter G) {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hxz : G.Adj x z) (hx : G.degree x = 3) (hy : G.degree y = 3) : False := by
  sorry

/-- **Claim 13.** If `xy` is an edge with `d(x) = d(y) = 3`, then `x` lies in a triangle. -/
theorem MinCounter.claim13 (hG : MinCounter G) {x y : V} (hxy : G.Adj x y)
    (hx : G.degree x = 3) (hy : G.degree y = 3) :
    ∃ a b, G.Adj x a ∧ G.Adj x b ∧ G.Adj a b := by
  sorry

/-- (5): every vertex of degree 3 has at most one neighbour of degree 3. -/
theorem MinCounter.deg3_nbrs (hG : MinCounter G) (x : V) (hx : G.degree x = 3) :
    ((G.neighborFinset x).filter fun y => G.degree y = 3).card ≤ 1 := by
  sorry

end Claims

/-- **Discharging.** If every degree is at least 3 and every vertex of degree 3 has at most one
neighbour of degree 3, then `3 |E| ≥ 5 |V|`. -/
theorem discharging {V : Type} [Fintype V] (G : SimpleGraph V) (h3 : ∀ v, 3 ≤ G.degree v)
    (h5 : ∀ x, G.degree x = 3 → ((G.neighborFinset x).filter fun y => G.degree y = 3).card ≤ 1) :
    5 * Fintype.card V ≤ 3 * G.edgeFinset.card := by
  sorry

/-- **Kostochka–Yancey (Ore's conjecture for `k = 4`).** Every 4-critical graph satisfies
`ρ_G(V) ≤ 2`, i.e. `3 |E| ≥ 5 |V| - 2`. -/
theorem pot_univ_le_two : ∀ (N : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V),
    Fintype.card V = N → IsCritical4 G → pot G univ ≤ 2 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro V _ G hN hG
  by_contra hbig
  push Not at hbig
  have hsmall : SmallColorable N :=
    smallColorable_of_minimal N fun W _ H hW hH => ih _ hW W H rfl hH
  have hmin : MinCounter G := ⟨hG, hbig, hN ▸ hsmall⟩
  have h5 := discharging G hG.three_le_degree hmin.deg3_nbrs
  have hE : eIn G univ = G.edgeFinset.card := by
    unfold eIn; congr 1; exact filter_true_of_mem fun e _ v _ => mem_univ v
  have : pot G univ = 5 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) := by
    rw [pot, hE, card_univ]
  omega

/-- Edge form: every 4-critical graph has at least `(5|V| - 2)/3` edges. -/
theorem five_mul_card_le {V : Type} [Fintype V] (G : SimpleGraph V) (hG : IsCritical4 G) :
    5 * Fintype.card V ≤ 3 * G.edgeFinset.card + 2 := by
  have h := pot_univ_le_two _ V G rfl hG
  have hE : eIn G univ = G.edgeFinset.card := by
    unfold eIn; congr 1; exact filter_true_of_mem fun e _ v _ => mem_univ v
  rw [pot, hE, card_univ] at h
  omega

end Grotzsch
