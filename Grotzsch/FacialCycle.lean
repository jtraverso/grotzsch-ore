/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Planar.FaceApex
public import LeanPool.K5MinorFreeChoosability.Planar.Nonplanar
public import LeanPool.K5MinorFreeChoosability.Reach

/-!
# Non-separating chordless cycles of plane maps are facial

A combinatorial Jordan-curve fact for genus-zero rotation systems, proved by counting. It
generalises the triangle case (`PlaneMap.triangle_facial` of the planar list-colouring library)
to cycles of any length `k ≥ 3`.

A cycle is a map `c : ZMod k → V` that is injective with `c i ~ c (i + 1)` for all `i`.

`cycle_facial`: if the cycle `c` of a plane map has no chords and any two vertices
off the cycle that carry an edge are joined by a path avoiding the cycle, then the cycle bounds
a face, in one of its two orientations.

The proof splits each vertex `c i` at the two corners where a closed curve running just beside
the cycle would pass. The split rotation has the cycle as a new face cycle. Counting cycles and
Euler's inequality `eulerDefect_nonneg` then force a new component, which contradicts the
connectivity hypothesis unless the cycle was already a face.

`isPlanar_apexExtend_cycle`: under the same hypotheses, a new vertex adjacent to every vertex
of the cycle can be added keeping the graph planar.
-/

@[expose] public section

open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

namespace Grotzsch

section Perm

variable {D : Type*}

/-- If `π'` agrees with `π` on a block `f ⁻¹' {c}` preserved by `π`, then cycles of `π` inside
that block are cycles of `π'`. -/
theorem sameCycle_of_agree {β : Type*} {π π' : Perm D} (f : D → β) (hf : ∀ z, f (π z) = f z)
    {c : β} (hag : ∀ z, f z = c → π' z = π z) {d e : D} (hd : f d = c) (hde : SameCycle π d e) :
    SameCycle π' d e := by
  let s : Setoid D :=
    { r := fun a b => (f a = c ∧ f b = c ∧ SameCycle π' a b) ∨ (f a ≠ c ∧ f b ≠ c)
      iseqv := by
        refine ⟨fun a => ?_, fun {a b} h => ?_, fun {a b c'} h k => ?_⟩
        · by_cases h : f a = c
          · exact Or.inl ⟨h, h, SameCycle.refl _ _⟩
          · exact Or.inr ⟨h, h⟩
        · rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h2, h1, h3.symm⟩
          · exact Or.inr ⟨h2, h1⟩
        · rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ <;> rcases k with ⟨k1, k2, k3⟩ | ⟨k1, k2⟩
          · exact Or.inl ⟨h1, k2, h3.trans k3⟩
          · exact absurd h2 k1
          · exact absurd k1 h2
          · exact Or.inr ⟨h1, k2⟩ }
  have key : s d e := by
    refine sameCycle_of_step s (fun z => ?_) hde
    by_cases hz : f z = c
    · refine Or.inl ⟨hz, (hf z).trans hz, ?_⟩
      rw [← hag z hz]
      exact ⟨1, by simp⟩
    · exact Or.inr ⟨hz, fun h => hz ((hf z).symm.trans h)⟩
  rcases key with ⟨_, _, h⟩ | ⟨h, _⟩
  · exact h
  · exact absurd hd h

/-- The orbit of an element of a `k`-cycle `a 0 ↦ a 1 ↦ ⋯`. -/
theorem eq_of_sameCycle_cyc [Finite D] {k : ℕ} [NeZero k] {ψ : Perm D} {a : ZMod k → D}
    (h : ∀ i, ψ (a i) = a (i + 1)) {d : D} (hd : SameCycle ψ (a 0) d) : ∃ i, d = a i := by
  obtain ⟨n, hn⟩ := hd.exists_nat_pow_eq
  subst hn
  clear hd
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨i, hi⟩ := ih
    exact ⟨i + 1, by rw [pow_succ', Perm.mul_apply, hi, h]⟩

variable [DecidableEq D]

theorem mulSwap_mul_eq (σ α : Perm D) (p q : D) :
    σ * swap p q * α = σ * α * swap (α⁻¹ p) (α⁻¹ q) := by
  have h := swap_apply_apply α (α⁻¹ p) (α⁻¹ q)
  rw [show α (α⁻¹ p) = p by simp, show α (α⁻¹ q) = q by simp] at h
  rw [h]
  simp [mul_assoc]

/-- If `a j` lies on a `k`-cycle of `π` and `e` does not, multiplying by `swap (a j) e` merges
two cycles. -/
theorem cycleCount_mul_swap_cyc [Finite D] {k : ℕ} [NeZero k] {π : Perm D} {a : ZMod k → D}
    (h : ∀ i, π (a i) = a (i + 1)) (j : ZMod k) {e : D} (he : ∀ i, e ≠ a i) :
    cycleCount (π * swap (a j) e) + 1 = cycleCount π := by
  refine cycleCount_mul_swap_of_not_sameCycle fun hs => ?_
  have h0 : SameCycle π (a 0) (a j) := by
    have hpow : ∀ n : ℕ, (π ^ n) (a 0) = a (n : ZMod k) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', Perm.mul_apply, ih, h]; push_cast; rfl
    refine ⟨(j.val : ℤ), ?_⟩
    rw [zpow_natCast, hpow, ZMod.natCast_zmod_val]
  obtain ⟨i, hi⟩ := eq_of_sameCycle_cyc h (h0.trans hs)
  exact he i hi

end Perm

variable {V : Type*} {G : SimpleGraph V}

theorem fst_swap_of_fst_eq [DecidableEq V] {a b w : G.Dart} (h : a.fst = b.fst) :
    (swap a b w).fst = w.fst := by
  by_cases ha : w = a
  · subst ha; simp [h]
  by_cases hb : w = b
  · subst hb; simp [h]
  rw [swap_apply_of_ne_of_ne ha hb]

theorem fst_rot_inv (M : PlaneMap G) (g : G.Dart) : (M.rot⁻¹ g).fst = g.fst := by
  have := M.isRotationSystem.fst_apply (M.rot⁻¹ g)
  rw [show M.rot (M.rot⁻¹ g) = g by simp] at this
  exact this.symm

/-! ### Cycles given by maps from `ZMod k` -/

/-- `c 0, c 1, …, c (k - 1)` is a cycle of `G`. -/
structure IsCycleMap (G : SimpleGraph V) {k : ℕ} (c : ZMod k → V) : Prop where
  inj : Function.Injective c
  adj : ∀ i, G.Adj (c i) (c (i + 1))

/-- The cycle `c` has no chords. -/
def IsChordless (G : SimpleGraph V) {k : ℕ} (c : ZMod k → V) : Prop :=
  ∀ i j, G.Adj (c i) (c j) → j = i + 1 ∨ i = j + 1

/-- The cycle `c` is a face cycle of the rotation `ρ`, traversed as `c 0 → c 1 → ⋯`: at each
`c i`, the rotation takes the dart towards `c (i - 1)` to the dart towards `c (i + 1)`. -/
def IsCycFace (ρ : Perm G.Dart) {k : ℕ} (c : ZMod k → V) : Prop :=
  ∀ i (d e : G.Dart), d.fst = c i → d.snd = c (i - 1) → e.fst = c i → e.snd = c (i + 1) →
    ρ d = e

theorem IsCycleMap.reverse {k : ℕ} {c : ZMod k → V} (hc : IsCycleMap G c) :
    IsCycleMap G (fun i => c (-i)) where
  inj := hc.inj.comp neg_injective
  adj i := by
    have := (hc.adj (-i - 1)).symm
    rwa [show -i - 1 + 1 = -i by ring, show -i - 1 = -(i + 1) by ring] at this

theorem IsChordless.reverse {k : ℕ} {c : ZMod k → V} (h : IsChordless G c) :
    IsChordless G (fun i => c (-i)) := by
  intro i j hij
  rcases h (-i) (-j) hij with h1 | h1
  · right; linear_combination h1
  · left; linear_combination h1

variable [Finite V]

/-- **Non-separating chordless cycles are facial.** Let `c` be a chordless cycle of length
`k ≥ 3` of the plane map `M`. If any two vertices off the cycle that carry an edge are joined by
a path avoiding the cycle, then the cycle is a face cycle of `M`, in the orientation
`c 0 → c 1 → ⋯` or in the reverse one. -/
theorem cycle_facial (M : PlaneMap G) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    {c : ZMod k → V} (hc : IsCycleMap G c) (hch : IsChordless G c)
    (hconn : ∀ d e : G.Dart, d.fst ∉ Set.range c → e.fst ∉ Set.range c →
      RIn G (Set.range c)ᶜ d.fst e.fst) :
    IsCycFace M.rot c ∨ IsCycFace M.rot (fun i => c (-i)) := by
  sorry

open FaceApex in
/-- A face cycle can receive an apex. -/
theorem isPlanar_apexExtend_of_isCycFace (M : PlaneMap G) {k : ℕ} [NeZero k]
    {c : ZMod k → V} (hc : IsCycleMap G c) (h : IsCycFace M.rot c) :
    IsPlanar (apexExtend G (Set.range c)) := by
  sorry

/-- **Apex over a non-separating chordless cycle.** Under the hypotheses of
`cycle_facial`, a new vertex adjacent to every vertex of the cycle keeps the graph
planar. -/
theorem isPlanar_apexExtend_cycle (M : PlaneMap G) {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    {c : ZMod k → V} (hc : IsCycleMap G c) (hch : IsChordless G c)
    (hconn : ∀ d e : G.Dart, d.fst ∉ Set.range c → e.fst ∉ Set.range c →
      RIn G (Set.range c)ᶜ d.fst e.fst) :
    IsPlanar (apexExtend G (Set.range c)) := by
  rcases cycle_facial M hk hc hch hconn with h | h
  · exact isPlanar_apexExtend_of_isCycFace M hc h
  · have := isPlanar_apexExtend_of_isCycFace M hc.reverse h
    rwa [show Set.range (fun i => c (-i)) = Set.range c from
      (Equiv.neg (ZMod k)).surjective.range_comp c] at this

end Grotzsch
