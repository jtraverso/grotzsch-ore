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

section SplitPerm

variable {D ι β : Type*} [DecidableEq D]

/-- Product of the transpositions `swap (p i) (q i)` over a list of indices. -/
private def tauL (p q : ι → D) : List ι → Perm D
  | [] => 1
  | i :: L => tauL p q L * swap (p i) (q i)

/-- Number of nontrivial transpositions in a list. -/
private def cntL (p q : ι → D) : List ι → ℕ
  | [] => 0
  | i :: L => cntL p q L + if p i = q i then 0 else 1

private theorem map_swap_of_eq (f : D → β) {x y : D} (h : f x = f y) (z : D) :
    f (swap x y z) = f z := by
  by_cases hx : z = x
  · subst hx; simp [h]
  by_cases hy : z = y
  · subst hy; simp [h]
  rw [swap_apply_of_ne_of_ne hx hy]

private theorem cycleCount_mul_swap_eq' [Finite D] {π : Perm D} {p q : D} (h : SameCycle π p q) :
    cycleCount (π * swap p q) = cycleCount π + if p = q then 0 else 1 := by
  by_cases hpq : p = q
  · subst hpq; simp [swap_self, ← Perm.one_def]
  · simp only [hpq, ↓reduceIte]; exact cycleCount_mul_swap_of_sameCycle hpq h

private theorem cycleCount_le_mul_swap' [Finite D] (π : Perm D) (p q : D) :
    cycleCount π ≤ cycleCount (π * swap p q) + if p = q then 0 else 1 := by
  by_cases hpq : p = q
  · subst hpq; simp [swap_self, ← Perm.one_def]
  · simp only [hpq, ↓reduceIte]
    by_cases hs : SameCycle π p q
    · rw [cycleCount_mul_swap_of_sameCycle hpq hs]; omega
    · have := cycleCount_mul_swap_of_not_sameCycle hs; omega

variable {p q : ι → D} {f : D → β} {v : ι → β}

private theorem tauL_apply_of_ne (hp : ∀ i, f (p i) = v i) (hq : ∀ i, f (q i) = v i) (L : List ι)
    {d : D} (hd : ∀ i ∈ L, f d ≠ v i) : tauL p q L d = d := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    change tauL p q L (swap (p i) (q i) d) = d
    have h1 : d ≠ p i := fun h => hd i (by simp) (by rw [h, hp])
    have h2 : d ≠ q i := fun h => hd i (by simp) (by rw [h, hq])
    rw [swap_apply_of_ne_of_ne h1 h2]
    exact ih fun j hj => hd j (by simp [hj])

private theorem tauL_apply_of_eq (hp : ∀ i, f (p i) = v i) (hq : ∀ i, f (q i) = v i)
    (hv : Function.Injective v) (L : List ι) (hL : L.Nodup) {i : ι} (hi : i ∈ L) {d : D}
    (hd : f d = v i) : tauL p q L d = swap (p i) (q i) d := by
  induction L with
  | nil => simp at hi
  | cons j L ih =>
    change tauL p q L (swap (p j) (q j) d) = _
    rw [List.nodup_cons] at hL
    by_cases hij : i = j
    · subst hij
      refine tauL_apply_of_ne hp hq L fun i' hi' h => ?_
      rw [map_swap_of_eq f ((hp i).trans (hq i).symm), hd] at h
      exact hL.1 (hv h ▸ hi')
    · have hi' : i ∈ L := by simpa [hij] using hi
      have h1 : d ≠ p j := fun h => hij (hv (by rw [← hd, h, hp]))
      have h2 : d ≠ q j := fun h => hij (hv (by rw [← hd, h, hq]))
      rw [swap_apply_of_ne_of_ne h1 h2]
      exact ih hL.2 hi'

private theorem cycleCount_tauL [Finite D] (hp : ∀ i, f (p i) = v i) (hq : ∀ i, f (q i) = v i)
    (hv : Function.Injective v) {ρ : Perm D} (hf : ∀ z, f (ρ z) = f z)
    (hs : ∀ i, SameCycle ρ (p i) (q i)) (L : List ι) (hL : L.Nodup) :
    cycleCount (ρ * tauL p q L) = cycleCount ρ + cntL p q L := by
  induction L with
  | nil => simp [tauL, cntL]
  | cons i L ih =>
    rw [List.nodup_cons] at hL
    change cycleCount (ρ * (tauL p q L * swap (p i) (q i))) = cycleCount ρ +
      (cntL p q L + if p i = q i then 0 else 1)
    rw [← mul_assoc, cycleCount_mul_swap_eq', ih hL.2, add_assoc]
    refine sameCycle_of_agree f hf (c := v i) (fun z hz => ?_) (hp i) (hs i)
    change ρ (tauL p q L z) = ρ z
    rw [tauL_apply_of_ne hp hq L fun j hj h => hL.1 (hv (hz.symm.trans h) ▸ hj)]

private theorem cycleCount_le_tauL [Finite D] (ρ α : Perm D) (L : List ι) :
    cycleCount (ρ * α) ≤ cycleCount (ρ * tauL p q L * α) + cntL p q L := by
  induction L with
  | nil => simp [tauL, cntL]
  | cons i L ih =>
    have h := cycleCount_le_mul_swap' (ρ * tauL p q L * α) (α⁻¹ (p i)) (α⁻¹ (q i))
    rw [← mulSwap_mul_eq] at h
    simp only [(α⁻¹).injective.eq_iff] at h
    change _ ≤ cycleCount (ρ * (tauL p q L * swap (p i) (q i)) * α) +
      (cntL p q L + if p i = q i then 0 else 1)
    rw [← mul_assoc]
    omega

end SplitPerm

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
  classical
  have := Fintype.ofFinite V
  set ρ := M.rot with hρ
  have hrs := M.isRotationSystem
  set α := dartSymm G with hα
  have hz : ∀ n : ℕ, 0 < n → n < 3 → (n : ZMod k) ≠ 0 := fun n h0 h3 h => by
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd h0 h
    omega
  have two_ne : (2 : ZMod k) ≠ 0 := by exact_mod_cast hz 2 (by norm_num) (by norm_num)
  have nsp : ∀ i : ZMod k, c (i + 1) ≠ c (i - 1) := fun i h =>
    two_ne (by have := hc.inj h; linear_combination this)
  have hext : ∀ {d e : G.Dart}, d.fst = e.fst → d.snd = e.snd → d = e := fun h1 h2 =>
    (SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext h1 h2)
  let a : ZMod k → G.Dart := fun i => ⟨(c i, c (i + 1)), hc.adj i⟩
  let p : ZMod k → G.Dart := fun i => ⟨(c i, c (i - 1)), by
    have := (hc.adj (i - 1)).symm
    rwa [sub_add_cancel] at this⟩
  let q : ZMod k → G.Dart := fun i => ρ⁻¹ (a i)
  have hp : ∀ i, (p i).fst = c i := fun _ => rfl
  have hq : ∀ i, (q i).fst = c i := fun i => fst_rot_inv M (a i)
  have hρq : ∀ i, ρ (q i) = a i := fun i => by simp [q]
  have hpa : ∀ i, (a i).symm = p (i + 1) := fun i => hext rfl (by simp [a, p])
  have hρne : ∀ i (w : G.Dart), w.fst = c i → ρ w ≠ w := by
    intro i w hw hfix
    have key : ∀ e : G.Dart, e.fst = w.fst → e = w := fun e he =>
      ((hrs.sameCycle w e he.symm).eq_of_left hfix).symm
    have e1 := key (a i) hw.symm
    have e2 := key (p i) hw.symm
    exact nsp i (congrArg (fun d : G.Dart => d.snd) (e1.trans e2.symm))
  have hoff : ∀ i (w : G.Dart), w.fst = c i → w.snd ≠ c (i + 1) → w.snd ≠ c (i - 1) →
      w.snd ∉ Set.range c := by
    rintro i w hw h1 h2 ⟨m, hm⟩
    have hadj : G.Adj (c i) (c m) := by rw [← hw, hm]; exact w.adj
    rcases hch i m hadj with rfl | h
    · exact h1 hm.symm
    · exact h2 (by rw [← hm, h, add_sub_cancel_right])
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hfwd, hrev⟩ := hcon
  obtain ⟨j, hj⟩ : ∃ j, p j ≠ q j := by
    by_contra hall
    push Not at hall
    apply hfwd
    intro i d e hd1 hd2 he1 he2
    rw [hext (e := p i) hd1 hd2, hext (e := a i) he1 he2, hall i]
    exact hρq i
  set L' : List (ZMod k) := (Finset.univ.erase j).toList
  set L : List (ZMod k) := j :: L'
  have hL : L.Nodup := List.nodup_cons.2 ⟨by simp [L'], Finset.nodup_toList _⟩
  have hLmem : ∀ i, i ∈ L := fun i => by
    by_cases hij : i = j
    · simp [L, hij]
    · simp [L, L', hij]
  set σ := ρ * tauL p q L with hσ
  have σ_on : ∀ i (d : G.Dart), d.fst = c i → σ d = ρ (swap (p i) (q i) d) := fun i d hd => by
    change ρ (tauL p q L d) = _
    rw [tauL_apply_of_eq (f := fun d : G.Dart => d.fst) hp hq hc.inj L hL (hLmem i) hd]
  have σ_off : ∀ d : G.Dart, d.fst ∉ Set.range c → σ d = ρ d := fun d hd => by
    change ρ (tauL p q L d) = _
    rw [tauL_apply_of_ne (f := fun d : G.Dart => d.fst) hp hq L fun i _ h => hd ⟨i, h.symm⟩]
  have σ_b : ∀ i, σ (a i).symm = a (i + 1) := fun i => by
    rw [σ_on (i + 1) _ rfl, hpa, swap_apply_left, hρq]
  have hαinv : ∀ d, α⁻¹ d = d.symm := fun d => by
    rw [Perm.inv_eq_iff_eq, hα, dartSymm_apply, SimpleGraph.Dart.symm_symm]
  -- counting
  have hsplit : (numComponents ρ α : ℤ) + 1 ≤ numComponents σ α := by
    have hcs : cycleCount σ = cycleCount ρ + cntL p q L :=
      cycleCount_tauL (f := fun d : G.Dart => d.fst) hp hq hc.inj hrs.fst_apply
        (fun i => hrs.sameCycle _ _ ((hp i).trans (hq i).symm)) L hL
    have hcf : cycleCount (ρ * α) ≤ cycleCount (ρ * tauL p q L' * α) + cntL p q L' :=
      cycleCount_le_tauL ρ α L'
    have hcnt : cntL p q L = cntL p q L' + 1 := by simp [L, cntL, hj]
    have hσ' : σ * α = ρ * tauL p q L' * α * swap (α⁻¹ (p j)) (α⁻¹ (q j)) := by
      rw [← mulSwap_mul_eq, hσ, mul_assoc ρ]
      rfl
    have hback : ρ * tauL p q L' * α = σ * α * swap (α⁻¹ (p j)) (α⁻¹ (q j)) := by
      rw [hσ', mul_assoc _ (swap _ _), swap_mul_self, mul_one]
    have hcyc : ∀ i, (σ * α) (a i) = a (i + 1) := σ_b
    have hpj : α⁻¹ (p j) = a (j - 1) := by
      rw [hαinv]; exact hext rfl (by simp [a, p])
    have he : ∀ i, α⁻¹ (q j) ≠ a i := by
      intro i h
      rw [hαinv] at h
      have h' : q j = (a i).symm := by rw [← h, SimpleGraph.Dart.symm_symm]
      have hfst : c j = c (i + 1) := by rw [← hq j, h']; rfl
      have hi : i = j - 1 := by rw [hc.inj hfst]; ring
      apply hj
      rw [h', hi, hpa, sub_add_cancel]
    have hm := cycleCount_mul_swap_cyc hcyc (j - 1) he
    rw [← hpj, ← hback] at hm
    have h0 := M.eulerDefect_eq_zero
    have h1 := eulerDefect_nonneg σ α
    unfold eulerDefect at h0 h1
    rw [← hρ, ← hα] at h0
    omega
  -- but the split permutation is still connected
  set R := compSetoid σ α
  have hfρ : ∀ i (w : G.Dart), w.fst = c i → (ρ w).fst = c i := fun i w hw =>
    (hrs.fst_apply w).trans hw
  obtain ⟨ω, hω⟩ : ∃ ω : G.Dart, ω.fst ∉ Set.range c := by
    refine ⟨(ρ (p j)).symm, hoff j _ (hfρ j _ rfl) (fun h => hj ?_) (fun h => ?_)⟩
    · exact Perm.eq_inv_iff_eq.2 (hext (hfρ j _ rfl) h)
    · exact hρne j (p j) rfl (hext (hfρ j _ rfl) h)
  -- all darts at outer vertices are related
  have hΩ : ∀ d : G.Dart, d.fst ∉ Set.range c → R d ω := by
    have key : ∀ x y, RIn G (Set.range c)ᶜ x y → x ∉ Set.range c →
        ∀ d e : G.Dart, d.fst = x → e.fst = y → R d e := by
      intro x y h hx
      induction h with
      | refl =>
        intro d e hd he
        refine compSetoid_of_sameCycle_left ?_
        refine sameCycle_of_agree (fun d : G.Dart => d.fst) hrs.fst_apply (c := d.fst)
          (fun w hw => σ_off w (by rw [hw, hd]; exact hx)) rfl
          (hrs.sameCycle d e (hd.trans he.symm))
      | @tail u y _ hcb ih =>
        intro d e hd he
        let w : G.Dart := ⟨(u, y), hcb.1⟩
        have h1 := ih d w hd rfl
        have h2 : R w w.symm := compSetoid_right _ _ w
        have h3 : R w.symm e := by
          refine compSetoid_of_sameCycle_left ?_
          refine sameCycle_of_agree (fun d : G.Dart => d.fst) hrs.fst_apply (c := y)
            (fun w' hw' => σ_off w' (hw' ▸ hcb.2.2)) rfl
            (hrs.sameCycle _ _ he.symm)
        exact R.trans h1 (R.trans h2 h3)
    intro d hd
    exact key _ _ (hconn d ω hd hω) hd d ω rfl rfl
  -- the cycle darts are related to each other
  have hab : ∀ i, R (a i) (a i).symm := fun i => compSetoid_right _ _ (a i)
  have hba : ∀ i, R (a i).symm (a (i + 1)) := fun i => by
    rw [← σ_b i]; exact compSetoid_left _ _ _
  have hA0 : ∀ i, R (a 0) (a i) := by
    have hn : ∀ n : ℕ, R (a 0) (a (n : ZMod k)) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have := hba (n : ZMod k)
        push_cast
        exact R.trans ih (R.trans (hab _) this)
    intro i
    have := hn i.val
    rwa [ZMod.natCast_zmod_val] at this
  -- a cycle dart reaches an outer dart
  have hcyc : ∀ i, R (a i) ω := by
    unfold IsCycFace at hrev
    push Not at hrev
    obtain ⟨i, d, e, hd1, hd2, he1, he2, hne⟩ := hrev
    set m := -i with hm
    have hd2' : d.snd = c (m + 1) := by rw [hd2]; congr 1; ring
    have he2' : e.snd = c (m - 1) := by rw [he2]; congr 1; ring
    have hda : d = a m := hext hd1 hd2'
    have hns : (ρ d).snd ∉ Set.range c := by
      refine hoff m _ (hfρ m d hd1) (fun h => hρne m d hd1 (hext (hfρ m d hd1 |>.trans hd1.symm)
        (h.trans hd2'.symm))) (fun h => hne (hext ((hfρ m d hd1).trans he1.symm)
        (h.trans he2'.symm)))
    have hσd : σ d = ρ d := by
      rw [σ_on m d hd1, swap_apply_of_ne_of_ne]
      · intro h
        exact nsp m (by rw [← hd2', h])
      · intro h
        have h' : ρ d = a m := by rw [h]; exact hρq m
        exact hρne m d hd1 (h'.trans hda.symm)
    have hlink : R d ω := by
      have r1 : R d (ρ d) := by rw [← hσd]; exact compSetoid_left _ _ d
      exact R.trans r1 (R.trans (compSetoid_right _ _ (ρ d)) (hΩ _ hns))
    intro i'
    rw [hda] at hlink
    exact R.trans (R.symm (hA0 i')) (R.trans (hA0 m) hlink)
  -- every dart is related to `ω`
  have hall : ∀ d : G.Dart, R d ω := by
    intro d
    by_cases hd : d.fst ∈ Set.range c
    swap
    · exact hΩ d hd
    by_cases hd' : d.snd ∈ Set.range c
    swap
    · exact R.trans (compSetoid_right _ _ d) (hΩ d.symm hd')
    obtain ⟨i, hi⟩ := hd
    obtain ⟨m, hm⟩ := hd'
    have hadj : G.Adj (c i) (c m) := by rw [hi, hm]; exact d.adj
    rcases hch i m hadj with rfl | h
    · rw [hext (e := a i) hi.symm hm.symm]; exact hcyc i
    · have : d = (a m).symm := hext (by rw [← hi, h]; rfl) hm.symm
      rw [this]
      exact R.trans (R.symm (hab m)) (hcyc m)
  have hle : numComponents σ α ≤ 1 := by
    unfold numComponents numClasses
    refine Finite.card_le_one_iff_subsingleton.2 ⟨fun x y => ?_⟩
    induction x using Quotient.inductionOn with
    | h d =>
    induction y using Quotient.inductionOn with
    | h e => exact Quotient.sound (R.trans (hall d) (R.symm (hall e)))
  have : Nonempty G.Dart := ⟨a 0⟩
  have h1 := one_le_numComponents ρ α
  omega

open FaceApex in
/-- A face cycle can receive an apex. -/
theorem isPlanar_apexExtend_of_isCycFace (M : PlaneMap G) {k : ℕ} [NeZero k]
    {c : ZMod k → V} (hc : IsCycleMap G c) (h : IsCycFace M.rot c) :
    IsPlanar (apexExtend G (Set.range c)) := by
  classical
  let a : ZMod k → G.Dart := fun i => ⟨(c i, c (i + 1)), hc.adj i⟩
  have h₁ : ∀ i, M.facePerm (a i) = a (i + 1) := fun i => by
    rw [M.facePerm_apply]
    exact h (i + 1) _ _ rfl (by simp [a]) rfl rfl
  have hmem : ∀ e : F M (a 0), ∃ i, e.1 = a i := fun e => eq_of_sameCycle_cyc h₁ e.2
  have hinj : ∀ e e' : F M (a 0), e.1.fst = e'.1.fst → e = e' := by
    intro e e' hee
    obtain ⟨i, hi⟩ := hmem e
    obtain ⟨j, hj⟩ := hmem e'
    apply Subtype.ext
    rw [hi, hj] at hee ⊢
    rw [hc.inj hee]
  have hpow : ∀ n : ℕ, (M.facePerm ^ n) (a 0) = a (n : ZMod k) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Perm.mul_apply, ih, h₁]; push_cast; rfl
  have hverts : faceVerts M (a 0) = Set.range c := by
    ext v
    constructor
    · rintro ⟨e, rfl⟩
      obtain ⟨i, hi⟩ := hmem e
      exact ⟨i, by rw [hi]⟩
    · rintro ⟨i, rfl⟩
      refine ⟨⟨a i, ⟨(i.val : ℤ), ?_⟩⟩, rfl⟩
      rw [zpow_natCast, hpow, ZMod.natCast_zmod_val]
  rw [← hverts]
  exact isPlanar_apexExtend_face M _ hinj

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
