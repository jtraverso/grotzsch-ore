/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Basic

/-!
# Correspondence (DP) colourings

A *correspondence* (matching assignment) on a vertex type `V` with colour type `C` is a
relation `M u v x y` ("colour `x` at `u` conflicts with colour `y` at `v`") which is
symmetric (`M u v x y ↔ M v u y x`) and a partial matching: for fixed `u, v, x` there is at
most one `y` with `M u v x y` (and, by symmetry, for fixed `u, v, y` at most one `x`).
For lists `L`, this is exactly a matching between `L u` and `L v` for every pair `u, v`,
i.e. a Dvořák--Postle cover.  An `(L, M)`-colouring picks `c v ∈ L v` such that
`M u v (c u) (c v)` fails for every edge `uv`.

Ordinary list colouring is the identity correspondence `M u v x y ↔ x = y`.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V C : Type*}

/-- `M` is a correspondence: a symmetric family of partial matchings between colours. -/
structure IsCorrespondence (M : V → V → C → C → Prop) : Prop where
  symm : ∀ u v x y, M u v x y → M v u y x
  unique : ∀ u v x y y', M u v x y → M u v x y' → y = y'

/-- An `(L, M)`-colouring (DP-colouring) of `G` exists. -/
def DPColourable (G : SimpleGraph V) (L : V → Finset C) (M : V → V → C → C → Prop) : Prop :=
  ∃ c : V → C, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → ¬ M u v (c u) (c v)

/-- DP-`k`-colourability with respect to the colour type `C`: every list assignment with
lists of size at least `k` and every correspondence admit a DP-colouring. -/
def DPColourableWith (G : SimpleGraph V) (C : Type*) (k : ℕ) : Prop :=
  ∀ (L : V → Finset C) (M : V → V → C → C → Prop), IsCorrespondence M →
    (∀ v, k ≤ (L v).card) → DPColourable G L M

namespace IsCorrespondence

variable {M : V → V → C → C → Prop}

theorem unique_left (hM : IsCorrespondence M) {u v : V} {x x' y : C} (h : M u v x y)
    (h' : M u v x' y) : x = x' :=
  hM.unique v u y x x' (hM.symm _ _ _ _ h) (hM.symm _ _ _ _ h')

theorem iff_symm (hM : IsCorrespondence M) {u v : V} {x y : C} : M u v x y ↔ M v u y x :=
  ⟨hM.symm _ _ _ _, hM.symm _ _ _ _⟩

/-- The identity correspondence, giving ordinary list colouring. -/
theorem eq : IsCorrespondence (fun (_ _ : V) (x y : C) => x = y) :=
  ⟨fun _ _ _ _ h => h.symm, fun _ _ _ _ _ h h' => h.symm.trans h'⟩

/-- At most one colour of a list conflicts with a given colour at a neighbour. -/
theorem card_filter_le_one (hM : IsCorrespondence M) (u v : V) (x : C) (T : Finset C)
    [DecidablePred (M u v x)] : (T.filter (M u v x)).card ≤ 1 :=
  Finset.card_le_one.2 fun _ ha _ hb =>
    hM.unique u v x _ _ (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2

/-- Removing the colours conflicting with one colour removes at most one element. -/
theorem card_filter_not_ge (hM : IsCorrespondence M) (u v : V) (x : C) (T : Finset C)
    [DecidablePred (M u v x)] : T.card ≤ (T.filter (fun y => ¬ M u v x y)).card + 1 := by
  have h := Finset.card_filter_add_card_filter_not (s := T) (M u v x)
  have := hM.card_filter_le_one u v x T
  omega

end IsCorrespondence

theorem dpColourable_eq_iff_listColourable {G : SimpleGraph V} {L : V → Finset C} :
    DPColourable G L (fun _ _ x y => x = y) ↔ ListColourable G L := by
  constructor
  · rintro ⟨c, hc, hp⟩
    exact ⟨SimpleGraph.Coloring.mk c (fun {a b} hab => hp a b hab), hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc, fun a b hab => c.valid hab⟩

end LeanPool.K5MinorFreeChoosability
