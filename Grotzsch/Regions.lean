/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Grotzsch.FacialCycle

/-!
# Regions of a subgraph of a plane map

A combinatorial Jordan–Schoenflies-type theorem for rotation systems.

Let `M` be a plane map of `G` and `H ≤ G` a subgraph. The rotation of `M` induces a rotation on
the darts of `H`: the next dart of `H` in `M.rot`-order (`subRot`, a first-return map).
* **J0** (`restrictMap`): the induced rotation is again a plane map (deleting edges does not
  increase the genus).
* A dart `d` of `G` at a vertex of `H` lies in a *gap* of the induced rotation; `IsNextH d e` says
  that `e` is the first dart of `H` reached from `d` by rotating. The gap belongs to the face of `H`
  through `e`.
* **R1** (`sameCycle_of_rIn`): if `H` is connected, all darts leading into one component of
  `G - V(H)` lie in gaps of the same face of `H`.
* **R2** (`sameCycle_of_chord`): both ends of a chord of `H` lie in gaps of the same face of `H`.
* **R3** (`eq_of_isNextH_of_face`): a face of `H` that is a face of `G` has empty gaps.
So every vertex off `H` lies in exactly one face ("region") of `H`, and edges never cross from one
region to another — the regions of the plane cut out by `H`.

The definitions were validated with `certo` (sweeps over every connected planar graph with at most
8 vertices, with a negative control on the torus where R1 fails).
-/

@[expose] public section

noncomputable section

open Classical Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

namespace Grotzsch

variable {V : Type*} {G H : SimpleGraph V}

/-- A dart of a subgraph, as a dart of the graph. -/
def toDart (hH : H ≤ G) (d : H.Dart) : G.Dart := ⟨d.toProd, hH d.adj⟩

@[simp] theorem toDart_fst (hH : H ≤ G) (d : H.Dart) : (toDart hH d).fst = d.fst := rfl

@[simp] theorem toDart_snd (hH : H ≤ G) (d : H.Dart) : (toDart hH d).snd = d.snd := rfl

@[simp] theorem toDart_symm (hH : H ≤ G) (d : H.Dart) : toDart hH d.symm = (toDart hH d).symm :=
  rfl

theorem toDart_injective (hH : H ≤ G) : Function.Injective (toDart hH) := fun a b h =>
  (SimpleGraph.Dart.ext_iff _ _).2 (congrArg (fun d : G.Dart => d.toProd) h :)

/-- The vertices of `H` that carry an edge. -/
def subVerts (H : SimpleGraph V) : Set V := {v | ∃ w, H.Adj v w}

/-- `d` is a dart of `H` (as a dart of `G`). -/
def InH (H : SimpleGraph V) (d : G.Dart) : Prop := H.Adj d.fst d.snd

variable [Fintype V]

/-! ### The induced rotation (first return) -/

/-- `σ` is the first-return permutation of `π` on the complement of `S`. -/
private def IsFR {D : Type*} (π σ : Perm D) (S : Set D) : Prop :=
  (∀ x ∈ S, σ x = x) ∧ ∀ x ∉ S, ∃ n, 0 < n ∧ (π ^ n) x = σ x ∧ σ x ∉ S ∧
    ∀ m, 0 < m → m < n → (π ^ m) x ∈ S

/-- Removing the elements of a finite set from the cycles of `π` one at a time gives the
first-return permutation, and never increases the Euler defect. -/
private theorem exists_isFR {D : Type*} [Finite D] [DecidableEq D] (π α : Perm D)
    (S : Finset D) : ∃ σ, IsFR π σ ↑S ∧ eulerDefect σ α ≤ eulerDefect π α := by
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨π, ⟨fun x hx => by simp at hx, fun x _ =>
      ⟨1, one_pos, by simp, by simp, fun m h1 h2 => by omega⟩⟩, le_rfl⟩
  | insert z S hz ih =>
    obtain ⟨σ, ⟨hfix, hret⟩, hle⟩ := ih
    refine ⟨removeFromCycle σ z, ⟨fun x hx => ?_, fun x hx => ?_⟩,
      (eulerDefect_removeFromCycle σ α z).trans hle⟩
    · rw [Finset.coe_insert, Set.mem_insert_iff] at hx
      rcases hx with rfl | hx
      · exact removeFromCycle_apply_self σ x
      · have hxz : x ≠ z := fun h => hz (h ▸ hx)
        rw [removeFromCycle_apply σ hxz, hfix x hx, ite_eq_right hxz]
    · rw [Finset.coe_insert, Set.mem_insert_iff, not_or] at hx
      obtain ⟨hxz, hxS⟩ := hx
      obtain ⟨n, hn, hpow, hσS, hmid⟩ := hret x hxS
      rw [removeFromCycle_apply σ hxz]
      by_cases hσx : σ x = z
      · rw [ite_eq_left hσx]
        obtain ⟨n', hn', hpow', hσS', hmid'⟩ := hret z hz
        have hzz : σ z ≠ z := fun h => hxz (σ.injective (hσx.trans h.symm))
        refine ⟨n + n', by omega, ?_, ?_, fun m h1 h2 => ?_⟩
        · rw [add_comm, pow_add, Perm.mul_apply, hpow, hσx, hpow']
        · rw [Finset.coe_insert, Set.mem_insert_iff, not_or]; exact ⟨hzz, hσS'⟩
        · rw [Finset.coe_insert, Set.mem_insert_iff]
          rcases lt_trichotomy m n with h | rfl | h
          · exact Or.inr (hmid m h1 h)
          · exact Or.inl (hpow.trans hσx)
          · right
            have := hmid' (m - n) (by omega) (by omega)
            rwa [← hσx, ← hpow, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel h.le] at this
      · rw [ite_eq_right hσx]
        refine ⟨n, hn, hpow, ?_, fun m h1 h2 => ?_⟩
        · rw [Finset.coe_insert, Set.mem_insert_iff, not_or]; exact ⟨hσx, hσS⟩
        · rw [Finset.coe_insert]; exact Set.mem_insert_of_mem _ (hmid m h1 h2)

/-- Detaching the two darts of each edge meeting a finite set of darts never increases the
Euler defect. -/
private theorem exists_alpha (σ : Perm G.Dart) (T : Finset G.Dart) :
    ∃ α : Perm G.Dart, (∀ x, α x = if x ∈ T ∨ x.symm ∈ T then x else x.symm) ∧
      eulerDefect σ α ≤ eulerDefect σ (dartSymm G) := by
  induction T using Finset.induction_on with
  | empty => exact ⟨dartSymm G, fun x => by simp, le_rfl⟩
  | insert z T hz ih =>
    obtain ⟨α, hα, hle⟩ := ih
    by_cases hzs : z.symm ∈ T
    · refine ⟨α, fun x => ?_, hle⟩
      have hiff : (x ∈ insert z T ∨ x.symm ∈ insert z T) ↔ (x ∈ T ∨ x.symm ∈ T) := by
        simp only [Finset.mem_insert]
        constructor
        · rintro ((rfl | h) | (h | h))
          · exact Or.inr hzs
          · exact Or.inl h
          · left; rw [← SimpleGraph.Dart.symm_symm x, h]; exact hzs
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr (Or.inr h)
      simp only [hα, hiff]
    · have hzz : z ≠ z.symm := (SimpleGraph.Dart.symm_ne z).symm
      have hαz : α z = z.symm := by rw [hα, ite_eq_right (by tauto)]
      refine ⟨α * swap z z.symm, fun x => ?_,
        (eulerDefect_mul_swap_right hzz ⟨1, by simp [hαz]⟩).trans hle⟩
      rw [Perm.mul_apply]
      by_cases h1 : x = z
      · subst h1; rw [swap_apply_left, hα]; simp [hz, hzs]
      by_cases h2 : x = z.symm
      · subst h2; rw [swap_apply_right, hαz]; simp
      · rw [swap_apply_of_ne_of_ne h1 h2, hα]
        have h3 : x.symm ≠ z := fun h => h2 (by rw [← h, SimpleGraph.Dart.symm_symm])
        simp [Finset.mem_insert, h1, h3]

theorem exists_rot_pow_inH (M : PlaneMap G) (hH : H ≤ G) (d : H.Dart) :
    ∃ n : ℕ, 0 < n ∧ InH H ((M.rot ^ n) (toDart hH d)) :=
  ⟨orderOf M.rot, orderOf_pos _, by rw [pow_orderOf_eq_one]; exact d.adj⟩

theorem exists_rot_inv_pow_inH (M : PlaneMap G) (hH : H ≤ G) (d : H.Dart) :
    ∃ n : ℕ, 0 < n ∧ InH H ((M.rot⁻¹ ^ n) (toDart hH d)) :=
  ⟨orderOf M.rot⁻¹, orderOf_pos _, by rw [pow_orderOf_eq_one]; exact d.adj⟩

/-- The next dart of `H` after `d` in rotation order. -/
def subRotFun (M : PlaneMap G) (hH : H ≤ G) (d : H.Dart) : H.Dart :=
  ⟨((M.rot ^ Nat.find (exists_rot_pow_inH M hH d)) (toDart hH d)).toProd,
    (Nat.find_spec (exists_rot_pow_inH M hH d)).2⟩

/-- The previous dart of `H` before `d` in rotation order. -/
def subRotInvFun (M : PlaneMap G) (hH : H ≤ G) (d : H.Dart) : H.Dart :=
  ⟨((M.rot⁻¹ ^ Nat.find (exists_rot_inv_pow_inH M hH d)) (toDart hH d)).toProd,
    (Nat.find_spec (exists_rot_inv_pow_inH M hH d)).2⟩

omit [Fintype V] in
theorem rot_pow_fst (M : PlaneMap G) (n : ℕ) (x : G.Dart) : ((M.rot ^ n) x).fst = x.fst := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, M.isRotationSystem.fst_apply, ih]

private theorem inv_pow_pow_apply {D : Type*} (π : Perm D) (x : D) {n k : ℕ} (h : n ≤ k) :
    (π⁻¹ ^ n) ((π ^ k) x) = (π ^ (k - n)) x := by
  rw [inv_pow, Perm.inv_eq_iff_eq, ← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' h]

private theorem pow_inv_pow_apply {D : Type*} (π : Perm D) (x : D) {n k : ℕ} (h : n ≤ k) :
    (π ^ n) ((π⁻¹ ^ k) x) = (π⁻¹ ^ (k - n)) x := by
  have := inv_pow_pow_apply π⁻¹ x h
  rwa [inv_inv] at this

theorem subRotInvFun_subRotFun (M : PlaneMap G) (hH : H ≤ G) (d : H.Dart) :
    subRotInvFun M hH (subRotFun M hH d) = d := by
  apply toDart_injective hH
  have hk := Nat.find_spec (exists_rot_pow_inH M hH d)
  have hmin : ∀ m < Nat.find (exists_rot_pow_inH M hH d),
      ¬ (0 < m ∧ InH H ((M.rot ^ m) (toDart hH d))) := fun m hm => Nat.find_min _ hm
  set k := Nat.find (exists_rot_pow_inH M hH d) with hkdef
  have hy : toDart hH (subRotFun M hH d) = (M.rot ^ k) (toDart hH d) := rfl
  have hfind : Nat.find (exists_rot_inv_pow_inH M hH (subRotFun M hH d)) = k := by
    rw [Nat.find_eq_iff]
    refine ⟨⟨hk.1, ?_⟩, fun n hn hn' => ?_⟩
    · rw [hy, inv_pow_pow_apply _ _ le_rfl, Nat.sub_self, pow_zero]; exact d.adj
    · rw [hy, inv_pow_pow_apply _ _ hn.le] at hn'
      exact hmin (k - n) (by omega) ⟨by omega, hn'.2⟩
  change (M.rot⁻¹ ^ Nat.find (exists_rot_inv_pow_inH M hH (subRotFun M hH d)))
    (toDart hH (subRotFun M hH d)) = _
  rw [hfind, hy, inv_pow_pow_apply _ _ le_rfl, Nat.sub_self, pow_zero, Perm.one_apply]

theorem subRotFun_subRotInvFun (M : PlaneMap G) (hH : H ≤ G) (d : H.Dart) :
    subRotFun M hH (subRotInvFun M hH d) = d := by
  apply toDart_injective hH
  have hk := Nat.find_spec (exists_rot_inv_pow_inH M hH d)
  have hmin : ∀ m < Nat.find (exists_rot_inv_pow_inH M hH d),
      ¬ (0 < m ∧ InH H ((M.rot⁻¹ ^ m) (toDart hH d))) := fun m hm => Nat.find_min _ hm
  set k := Nat.find (exists_rot_inv_pow_inH M hH d) with hkdef
  have hy : toDart hH (subRotInvFun M hH d) = (M.rot⁻¹ ^ k) (toDart hH d) := rfl
  have hfind : Nat.find (exists_rot_pow_inH M hH (subRotInvFun M hH d)) = k := by
    rw [Nat.find_eq_iff]
    refine ⟨⟨hk.1, ?_⟩, fun n hn hn' => ?_⟩
    · rw [hy, pow_inv_pow_apply _ _ le_rfl, Nat.sub_self, pow_zero]; exact d.adj
    · rw [hy, pow_inv_pow_apply _ _ hn.le] at hn'
      exact hmin (k - n) (by omega) ⟨by omega, hn'.2⟩
  change (M.rot ^ Nat.find (exists_rot_pow_inH M hH (subRotInvFun M hH d)))
    (toDart hH (subRotInvFun M hH d)) = _
  rw [hfind, hy, pow_inv_pow_apply _ _ le_rfl, Nat.sub_self, pow_zero, Perm.one_apply]

/-- The rotation induced on a subgraph. -/
def subRot (M : PlaneMap G) (hH : H ≤ G) : Perm H.Dart where
  toFun := subRotFun M hH
  invFun := subRotInvFun M hH
  left_inv := subRotInvFun_subRotFun M hH
  right_inv := subRotFun_subRotInvFun M hH

theorem subRot_apply (M : PlaneMap G) (hH : H ≤ G) (d : H.Dart) :
    toDart hH (subRot M hH d) = (M.rot ^ Nat.find (exists_rot_pow_inH M hH d)) (toDart hH d) :=
  rfl

private theorem sameCycle_subRot_of_pow (M : PlaneMap G) (hH : H ≤ G) (n : ℕ) :
    ∀ d e : H.Dart, (M.rot ^ n) (toDart hH d) = toDart hH e → SameCycle (subRot M hH) d e := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro d e h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, Perm.one_apply] at h
    rw [toDart_injective hH h]
  · have hle : Nat.find (exists_rot_pow_inH M hH d) ≤ n :=
      Nat.find_min' _ ⟨hn, by rw [h]; exact e.adj⟩
    have hk := (Nat.find_spec (exists_rot_pow_inH M hH d)).1
    have h2 : (M.rot ^ (n - Nat.find (exists_rot_pow_inH M hH d)))
        (toDart hH (subRot M hH d)) = toDart hH e := by
      rw [subRot_apply, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hle, h]
    exact (show SameCycle (subRot M hH) d (subRot M hH d) from ⟨1, by simp⟩).trans
      (ih _ (by omega) _ _ h2)

theorem isRotationSystem_subRot (M : PlaneMap G) (hH : H ≤ G) :
    IsRotationSystem H (subRot M hH) := by
  refine ⟨fun d => ?_, fun d e hde => ?_⟩
  · change (toDart hH (subRot M hH d)).fst = (toDart hH d).fst
    rw [subRot_apply, rot_pow_fst]
  · obtain ⟨n, hn⟩ :=
      (M.isRotationSystem.sameCycle (toDart hH d) (toDart hH e) hde).exists_nat_pow_eq
    exact sameCycle_subRot_of_pow M hH n d e hn

/-- **J0.** The induced rotation of a subgraph of a plane map has Euler defect zero. -/
theorem eulerDefect_subRot (M : PlaneMap G) (hH : H ≤ G) :
    eulerDefect (subRot M hH) (dartSymm H) = 0 := by
  set S : Finset G.Dart := Finset.univ.filter (fun x => ¬ InH H x) with hS
  have hmemS : ∀ x, x ∈ (S : Set G.Dart) ↔ ¬ InH H x := fun x => by simp [hS]
  obtain ⟨σ, ⟨hfix, hret⟩, hσle⟩ := exists_isFR M.rot (dartSymm G) S
  obtain ⟨α, hα, hαle⟩ := exists_alpha σ S
  let e : {x : G.Dart // InH H x} ≃ H.Dart :=
    { toFun := fun x => ⟨x.1.toProd, x.2⟩
      invFun := fun d => ⟨toDart hH d, d.adj⟩
      left_inv := fun x => rfl
      right_inv := fun d => rfl }
  let σs : Perm {x : G.Dart // InH H x} := e.permCongr.symm (subRot M hH)
  let αs : Perm {x : G.Dart // InH H x} := e.permCongr.symm (dartSymm H)
  have h1 : eulerDefect (subRot M hH) (dartSymm H) = eulerDefect σs αs := by
    rw [← eulerDefect_permCongr e σs αs]
    simp only [σs, αs, Equiv.apply_symm_apply]
  have h2 := eulerDefect_ofSubtype (fun x : G.Dart => InH H x) σs αs
  have h3 : ofSubtype σs = σ := by
    refine Equiv.ext fun x => ?_
    by_cases hx : InH H x
    · rw [ofSubtype_apply_of_mem σs hx]
      change toDart hH (subRot M hH ⟨x.toProd, hx⟩) = σ x
      rw [subRot_apply]
      obtain ⟨n, hn, hpow, hσS, hmid⟩ := hret x (by rw [hmemS]; exact not_not.2 hx)
      have hσH : InH H (σ x) := by rw [hmemS, not_not] at hσS; exact hσS
      have hfind : Nat.find (exists_rot_pow_inH M hH ⟨x.toProd, hx⟩) = n := by
        rw [Nat.find_eq_iff]
        refine ⟨⟨hn, ?_⟩, fun m hm hm' => ?_⟩
        · change InH H ((M.rot ^ n) x); rw [hpow]; exact hσH
        · exact (hmemS _).1 (hmid m hm'.1 hm) hm'.2
      rw [hfind]; exact hpow
    · rw [ofSubtype_apply_of_not_mem σs hx, hfix x ((hmemS x).2 hx)]
  have h4 : ofSubtype αs = α := by
    refine Equiv.ext fun x => ?_
    by_cases hx : InH H x
    · rw [ofSubtype_apply_of_mem αs hx]
      change toDart hH (dartSymm H ⟨x.toProd, hx⟩) = α x
      have hx' : InH H x.symm := hx.symm
      rw [hα, ite_eq_right]
      · rfl
      · simp only [← Finset.mem_coe, hmemS, not_not, not_or]; exact ⟨hx, hx'⟩
    · rw [ofSubtype_apply_of_not_mem αs hx, hα, ite_eq_left (Or.inl (by simpa [hS] using hx))]
  have h0 := M.eulerDefect_eq_zero
  have hnn := eulerDefect_nonneg (subRot M hH) (dartSymm H)
  rw [h1, ← h2, h3, h4] at hnn ⊢
  linarith

/-- The plane map induced on a subgraph. -/
def restrictMap (M : PlaneMap G) (hH : H ≤ G) : PlaneMap H where
  rot := subRot M hH
  isRotationSystem := isRotationSystem_subRot M hH
  eulerDefect_eq_zero := eulerDefect_subRot M hH

/-! ### Gaps and regions -/

/-- `e` is the first dart of `H` reached from the dart `d` of `G` by rotating (`d` itself if `d`
is a dart of `H`): `d` lies in the gap of the induced rotation that ends at `e`. -/
def IsNextH (M : PlaneMap G) (hH : H ≤ G) (d : G.Dart) (e : H.Dart) : Prop :=
  ∃ n : ℕ, (M.rot ^ n) d = toDart hH e ∧ ∀ m < n, ¬ InH H ((M.rot ^ m) d)

theorem exists_isNextH (M : PlaneMap G) (hH : H ≤ G) {d : G.Dart} (hd : d.fst ∈ subVerts H) :
    ∃ e, IsNextH M hH d e := by
  obtain ⟨w, hw⟩ := hd
  let a : H.Dart := ⟨(d.fst, w), hw⟩
  obtain ⟨n, hn⟩ := (M.isRotationSystem.sameCycle d (toDart hH a) rfl).exists_nat_pow_eq
  have hex : ∃ n : ℕ, InH H ((M.rot ^ n) d) := ⟨n, by rw [hn]; exact hw⟩
  exact ⟨⟨((M.rot ^ Nat.find hex) d).toProd, Nat.find_spec hex⟩, Nat.find hex, rfl,
    fun m hm => Nat.find_min hex hm⟩

omit [Fintype V] in
theorem isNextH_unique (M : PlaneMap G) (hH : H ≤ G) {d : G.Dart} {e e' : H.Dart}
    (he : IsNextH M hH d e) (he' : IsNextH M hH d e') : e = e' := by
  obtain ⟨n, hn, hmin⟩ := he
  obtain ⟨n', hn', hmin'⟩ := he'
  have : n = n' := by
    rcases lt_trichotomy n n' with h | h | h
    · exact (hmin' n h (by rw [hn]; exact e.adj)).elim
    · exact h
    · exact (hmin n' h (by rw [hn']; exact e'.adj)).elim
  subst this
  exact toDart_injective hH (hn.symm.trans hn')

omit [Fintype V] in
theorem isNextH_fst (M : PlaneMap G) (hH : H ≤ G) {d : G.Dart} {e : H.Dart}
    (h : IsNextH M hH d e) : e.fst = d.fst := by
  obtain ⟨n, hn, -⟩ := h
  rw [← toDart_fst hH e, ← hn, rot_pow_fst]

omit [Fintype V] in
theorem isNextH_self (M : PlaneMap G) (hH : H ≤ G) {d : G.Dart} (h : InH H d) :
    IsNextH M hH d ⟨d.toProd, h⟩ :=
  ⟨0, rfl, fun m hm => absurd hm (Nat.not_lt_zero m)⟩

omit [Fintype V] in
theorem eq_of_isNextH_of_inH (M : PlaneMap G) (hH : H ≤ G) {d : G.Dart} {e : H.Dart}
    (hd : InH H d) (h : IsNextH M hH d e) : d = toDart hH e := by
  obtain ⟨n, hn, hmin⟩ := h
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simpa using hn
  · exact (hmin 0 hpos (by simpa using hd)).elim

omit [Fintype V] in
theorem isNextH_rot_of_not (M : PlaneMap G) (hH : H ≤ G) {d : G.Dart} {e : H.Dart}
    (hd : ¬ InH H d) (h : IsNextH M hH d e) : IsNextH M hH (M.rot d) e := by
  obtain ⟨n, hn, hmin⟩ := h
  have hpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [pow_zero, Perm.one_apply] at hn
      exact (hd (by rw [hn]; exact e.adj)).elim
    · exact hpos
  refine ⟨n - 1, ?_, fun m hm hmH => hmin (m + 1) (by omega) ?_⟩
  · rw [← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hpos, hn]
  · rwa [pow_succ, Perm.mul_apply]

theorem isNextH_rot_subRot (M : PlaneMap G) (hH : H ≤ G) (d : H.Dart) :
    IsNextH M hH (M.rot (toDart hH d)) (subRot M hH d) := by
  have hk := (Nat.find_spec (exists_rot_pow_inH M hH d)).1
  refine ⟨Nat.find (exists_rot_pow_inH M hH d) - 1, ?_, fun m hm hmH => ?_⟩
  · rw [subRot_apply, ← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hk]
  · rw [← Perm.mul_apply, ← pow_succ] at hmH
    exact Nat.find_min _ (show m + 1 < Nat.find (exists_rot_pow_inH M hH d) by omega)
      ⟨by omega, hmH⟩

omit [Fintype V] in
theorem isNextH_trans (M : PlaneMap G) {H' : SimpleGraph V} (hH : H ≤ G) (hH' : H' ≤ G)
    (hHH' : H ≤ H') {x : G.Dart} {y : H'.Dart} {e : H.Dart} (hy : IsNextH M hH' x y)
    (he : IsNextH M hH (toDart hH' y) e) : IsNextH M hH x e := by
  obtain ⟨n1, h1, m1⟩ := hy
  obtain ⟨n2, h2, m2⟩ := he
  refine ⟨n2 + n1, by rw [pow_add, Perm.mul_apply, h1, h2], fun m hm hmH => ?_⟩
  by_cases hm1 : m < n1
  · exact m1 m hm1 (hHH' hmH)
  · have := m2 (m - n1) (by omega)
    rw [← h1, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel (by omega)] at this
    exact this hmH

omit [Fintype V] in
theorem isNextH_of_first (M : PlaneMap G) {H' : SimpleGraph V} (hH : H ≤ G) (hH' : H' ≤ G)
    (hHH' : H ≤ H') {x : G.Dart} {y : H'.Dart} {e : H.Dart} (hy : IsNextH M hH' x y)
    (he : IsNextH M hH x e) : IsNextH M hH (toDart hH' y) e := by
  obtain ⟨n1, h1, m1⟩ := hy
  obtain ⟨n2, h2, m2⟩ := he
  have hle : n1 ≤ n2 := by
    by_contra h
    exact m1 n2 (by omega) (by rw [h2]; exact hHH' e.adj)
  refine ⟨n2 - n1, ?_, fun m hm hmH => ?_⟩
  · rw [← h1, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hle, h2]
  · rw [← h1, ← Perm.mul_apply, ← pow_add] at hmH
    exact m2 (m + n1) (by omega) hmH

/-! ### Auxiliary results for R1 and R2 -/

/-- An edge whose two darts lie on one face of a plane map, and which can be removed without
separating its darts, cannot exist (removing it would make the Euler defect negative). -/
private theorem core_contra {D : Type*} [Finite D] [DecidableEq D] {σ α : Perm D}
    (h0 : eulerDefect σ α = 0) {z w : D} (hne : z ≠ w) (hα : α z = w)
    (hface : SameCycle (σ * α) z w) (hconn : compSetoid σ (α * swap z w) z w) : False := by
  have hαs : SameCycle α z w := ⟨1, by simp [hα]⟩
  have hc2 := cycleCount_mul_swap_of_sameCycle hne hαs
  have hc3 := cycleCount_mul_swap_of_sameCycle hne hface
  have hK : numComponents σ (α * swap z w) ≤ numComponents σ α :=
    numClasses_le_of_le (fun u v huv => compSetoid_le _ (compSetoid_left _ _)
      (rel_apply_of_mulSwap _ α z w (compSetoid_right _ _) hconn) huv)
  have hnn := eulerDefect_nonneg σ (α * swap z w)
  unfold eulerDefect at h0 hnn
  rw [← mul_assoc, hc3, hc2] at hnn
  push_cast at hnn
  omega

/-- Following the cycle of `π` through `x₀` inside `π'` (along an injection `i`): either `π'`
deviates somewhere, towards `y₁`, or the cycle of `π'` through `i x₀` stays in the image. -/
private theorem sameCycle_of_walk {X Y : Type*} [Finite Y] {π : Perm X} {π' : Perm Y} (i : X → Y)
    {x₀ : X} {y₀ y₁ : Y} (h0 : SameCycle π' (i x₀) y₀) (h1 : ∀ x, i x ≠ y₀)
    (h2 : ∀ x, SameCycle π x₀ x → π' (i x) ≠ i (π x) → π' (i x) = y₁) :
    SameCycle π' (i x₀) y₁ := by
  by_contra hne
  obtain ⟨n, hn⟩ := h0.exists_nat_pow_eq
  have key : ∀ k : ℕ, (π' ^ k) (i x₀) = i ((π ^ k) x₀) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs : SameCycle π x₀ ((π ^ k) x₀) := ⟨k, by simp⟩
      by_cases hdev : π' (i ((π ^ k) x₀)) = i (π ((π ^ k) x₀))
      · rw [pow_succ', Perm.mul_apply, ih, hdev, pow_succ', Perm.mul_apply]
      · exfalso
        apply hne
        rw [← h2 _ hs hdev, ← ih]
        exact ⟨(k + 1 : ℕ), by rw [zpow_natCast, pow_succ', Perm.mul_apply]⟩
  exact h1 _ ((key n).symm.trans hn)

omit [Fintype V] in
private theorem rIn_split {s : Set V} {a b : V} (h : RIn G s a b) (hab : a ≠ b) :
    ∃ w, G.Adj a w ∧ w ∈ s ∧ w ≠ a ∧ RIn G (s \ {a}) w b := by
  induction h with
  | refl => exact absurd rfl hab
  | @tail c b' hac hcb ih =>
    by_cases hca : c = a
    · subst hca
      exact ⟨b', hcb.1, hcb.2.2, Ne.symm hab, RIn.refl _⟩
    · obtain ⟨w, h1, h2, h3, h4⟩ := ih (Ne.symm hca)
      exact ⟨w, h1, h2, h3, h4.tail hcb.1 ⟨hcb.2.1, hca⟩ ⟨hcb.2.2, Ne.symm hab⟩⟩

/-- The graph `H` with the edge of the dart `d` added. -/
def plusEdge (H : SimpleGraph V) (d : G.Dart) : SimpleGraph V :=
  H ⊔ SimpleGraph.fromEdgeSet {d.edge}

omit [Fintype V] in
theorem plusEdge_adj {d : G.Dart} {u v : V} :
    (plusEdge H d).Adj u v ↔ H.Adj u v ∨ (u = d.fst ∧ v = d.snd) ∨ (u = d.snd ∧ v = d.fst) := by
  have hne := d.adj.ne
  simp only [plusEdge, SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff,
    SimpleGraph.Dart.edge, Sym2.mk, Sym2.eq_iff]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne
      · exact hne.symm

omit [Fintype V] in
theorem le_plusEdge (H : SimpleGraph V) (d : G.Dart) : H ≤ plusEdge H d := le_sup_left

omit [Fintype V] in
theorem plusEdge_le (hH : H ≤ G) (d : G.Dart) : plusEdge H d ≤ G := fun u v h => by
  rcases plusEdge_adj.1 h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hH h
  · exact d.adj
  · exact d.adj.symm

/-- The dart `d` as a dart of `plusEdge H d`. -/
def newDart (H : SimpleGraph V) (d : G.Dart) : (plusEdge H d).Dart :=
  ⟨d.toProd, plusEdge_adj.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩

omit [Fintype V] in
private theorem dart_eq_of {W : SimpleGraph V} {x y : W.Dart} (h1 : x.fst = y.fst)
    (h2 : x.snd = y.snd) : x = y :=
  (SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext h1 h2)

omit [Fintype V] in
theorem dart_plusEdge_cases {d : G.Dart} (y : (plusEdge H d).Dart) :
    H.Adj y.fst y.snd ∨ y = newDart H d ∨ y = (newDart H d).symm := by
  rcases plusEdge_adj.1 y.adj with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl (dart_eq_of h1 h2))
  · exact Or.inr (Or.inr (dart_eq_of h1 h2))

omit [Fintype V] in
theorem mem_subVerts_plusEdge {d : G.Dart} (hd : d.fst ∈ subVerts H) {v : V} :
    v ∈ subVerts (plusEdge H d) ↔ v ∈ subVerts H ∨ v = d.snd := by
  constructor
  · rintro ⟨w, h⟩
    rcases plusEdge_adj.1 h with h | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl ⟨w, h⟩
    · exact Or.inl hd
    · exact Or.inr rfl
  · rintro (⟨w, h⟩ | rfl)
    · exact ⟨w, le_plusEdge H d h⟩
    · exact ⟨d.fst, plusEdge_adj.2 (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

omit [Fintype V] in
theorem reachable_plusEdge {d : G.Dart} (hd : d.fst ∈ subVerts H)
    (hconn : ∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b) :
    ∀ a ∈ subVerts (plusEdge H d), ∀ b ∈ subVerts (plusEdge H d),
      (plusEdge H d).Reachable a b := by
  have key : ∀ a ∈ subVerts (plusEdge H d), (plusEdge H d).Reachable a d.fst := by
    intro a ha
    rcases (mem_subVerts_plusEdge hd).1 ha with ha | rfl
    · exact (hconn a ha d.fst hd).mono (le_plusEdge H d)
    · exact (plusEdge_adj.2 (Or.inr (Or.inr ⟨rfl, rfl⟩))).reachable
  intro a ha b hb
  exact (key a ha).trans (key b hb).symm

/-- In the rotation induced on `plusEdge H d`, the dart after `d` is the next dart of `H`. -/
theorem subRot_newDart (M : PlaneMap G) (hH : H ≤ G) {d : G.Dart} (hd : d.fst ∈ subVerts H)
    (hnot : ¬ InH H d) {e₁ : H.Dart} (h₁ : IsNextH M hH d e₁) :
    subRot M (plusEdge_le hH d) (newDart H d) = toDart (le_plusEdge H d) e₁ := by
  have hz := isNextH_of_first M hH (plusEdge_le hH d) (le_plusEdge H d)
    (isNextH_rot_subRot M (plusEdge_le hH d) (newDart H d)) (isNextH_rot_of_not M hH hnot h₁)
  rcases dart_plusEdge_cases (subRot M (plusEdge_le hH d) (newDart H d)) with h | h | h
  · exact toDart_injective (plusEdge_le hH d) (eq_of_isNextH_of_inH M hH h hz)
  · exfalso
    obtain ⟨w, hw⟩ := hd
    let a : (plusEdge H d).Dart := ⟨(d.fst, w), le_plusEdge H d hw⟩
    have hs := (isRotationSystem_subRot M (plusEdge_le hH d)).sameCycle (newDart H d) a rfl
    have := hs.eq_of_left h
    exact hnot (by rw [show d = toDart (plusEdge_le hH d) (newDart H d) from rfl, this]; exact hw)
  · exfalso
    have hf := (isRotationSystem_subRot M (plusEdge_le hH d)).fst_apply (newDart H d)
    rw [h] at hf
    exact d.adj.ne hf.symm

/-- How the rotation induced on `plusEdge H d` compares with the one induced on `H`. -/
theorem subRot_plusEdge_cases (M : PlaneMap G) (hH : H ≤ G) (d : G.Dart) (x : H.Dart) :
    subRot M (plusEdge_le hH d) (toDart (le_plusEdge H d) x) =
        toDart (le_plusEdge H d) (subRot M hH x) ∨
      (subRot M (plusEdge_le hH d) (toDart (le_plusEdge H d) x) = newDart H d ∧
        IsNextH M hH d (subRot M hH x)) ∨
      (subRot M (plusEdge_le hH d) (toDart (le_plusEdge H d) x) = (newDart H d).symm ∧
        IsNextH M hH d.symm (subRot M hH x)) := by
  have hz := isNextH_of_first M hH (plusEdge_le hH d) (le_plusEdge H d)
    (isNextH_rot_subRot M (plusEdge_le hH d) (toDart (le_plusEdge H d) x))
    (isNextH_rot_subRot M hH x)
  rcases dart_plusEdge_cases (subRot M (plusEdge_le hH d) (toDart (le_plusEdge H d) x))
    with h | h | h
  · exact Or.inl (toDart_injective (plusEdge_le hH d) (eq_of_isNextH_of_inH M hH h hz))
  · rw [h] at hz
    exact Or.inr (Or.inl ⟨h, hz⟩)
  · rw [h] at hz
    exact Or.inr (Or.inr ⟨h, hz⟩)

omit [Fintype V] in
theorem eq_symm_newDart {d : G.Dart} (hd' : d.snd ∉ subVerts H) (y : (plusEdge H d).Dart)
    (hy : y.fst = d.snd) : y = (newDart H d).symm := by
  rcases dart_plusEdge_cases y with h | h | h
  · exact (hd' (hy ▸ ⟨y.snd, h⟩)).elim
  · exact (d.adj.ne (by rw [← hy, h]; rfl)).elim
  · exact h

/-- Connectivity of the darts of `H'` at vertices of a connected `H ≤ H'`, after detaching the
two darts of an edge not in `H`. -/
private theorem compSetoid_of_reach (M : PlaneMap G) {H' : SimpleGraph V} (hH' : H' ≤ G)
    (hHH' : H ≤ H') (hconn : ∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b)
    {z : H'.Dart} (hz : ¬ H.Adj z.fst z.snd) {x y : H'.Dart} (hx : x.fst ∈ subVerts H)
    (hy : y.fst ∈ subVerts H) :
    compSetoid (subRot M hH') (dartSymm H' * swap z z.symm) x y := by
  obtain ⟨p⟩ := hconn _ hx _ hy
  suffices key : ∀ (u w : V) (p : H.Walk u w) (x y : H'.Dart), x.fst = u → y.fst = w →
      compSetoid (subRot M hH') (dartSymm H' * swap z z.symm) x y from key _ _ p x y rfl rfl
  intro u w p
  induction p with
  | nil =>
    intro x y hx hy
    exact compSetoid_of_sameCycle_left
      ((isRotationSystem_subRot M hH').sameCycle x y (hx.trans hy.symm))
  | @cons u v w' huv p ih =>
    intro x y hx hy
    let c : H'.Dart := ⟨(u, v), hHH' huv⟩
    have h1 : compSetoid (subRot M hH') (dartSymm H' * swap z z.symm) x c :=
      compSetoid_of_sameCycle_left ((isRotationSystem_subRot M hH').sameCycle x c hx)
    have hcz : c ≠ z := fun h => hz (by rw [← h]; exact huv)
    have hcz' : c ≠ z.symm := fun h => hz (by rw [← SimpleGraph.Dart.symm_symm z, ← h]; exact huv.symm)
    have h2 : compSetoid (subRot M hH') (dartSymm H' * swap z z.symm) c c.symm := by
      have := compSetoid_right (subRot M hH') (dartSymm H' * swap z z.symm) c
      rwa [Perm.mul_apply, swap_apply_of_ne_of_ne hcz hcz', dartSymm_apply] at this
    exact (compSetoid _ _).trans h1 ((compSetoid _ _).trans h2 (ih c.symm y rfl hy))

/-- **R2**, proved before R1 since R1 uses it. -/
private theorem sameCycle_of_chord_aux (M : PlaneMap G) (hH : H ≤ G)
    (hconn : ∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b)
    {d : G.Dart} (hd : d.fst ∈ subVerts H) (hd' : d.snd ∈ subVerts H) (hnot : ¬ InH H d)
    {e₁ e₂ : H.Dart} (h₁ : IsNextH M hH d e₁) (h₂ : IsNextH M hH d.symm e₂) :
    SameCycle (restrictMap M hH).facePerm e₁ e₂ := by
  by_contra hne
  have hF1 := subRot_newDart M hH hd hnot h₁
  have hstep : SameCycle (subRot M (plusEdge_le hH d) * dartSymm (plusEdge H d))
      (newDart H d).symm (toDart (le_plusEdge H d) e₁) := ⟨1, by simp [hF1]⟩
  have hface : SameCycle (subRot M (plusEdge_le hH d) * dartSymm (plusEdge H d))
      (newDart H d) (newDart H d).symm := by
    have hw := sameCycle_of_walk (π := (restrictMap M hH).facePerm)
      (π' := subRot M (plusEdge_le hH d) * dartSymm (plusEdge H d)) (toDart (le_plusEdge H d))
      (x₀ := e₁) (y₀ := (newDart H d).symm) (y₁ := newDart H d) hstep.symm ?_ ?_
    · exact (hstep.trans hw).symm
    · intro x hx
      apply hnot
      have := congrArg (fun y : (plusEdge H d).Dart => y.symm) hx
      simp only [SimpleGraph.Dart.symm_symm] at this
      rw [show d = toDart (plusEdge_le hH d) (newDart H d) from rfl, ← this]
      exact x.adj.symm
    · intro x hx hdev
      change subRot M (plusEdge_le hH d) (toDart (le_plusEdge H d) x.symm) ≠
        toDart (le_plusEdge H d) (subRot M hH x.symm) at hdev
      change subRot M (plusEdge_le hH d) (toDart (le_plusEdge H d) x.symm) = _
      rcases subRot_plusEdge_cases M hH d x.symm with h | ⟨h, -⟩ | ⟨-, hn⟩
      · exact absurd h hdev
      · exact h
      · exfalso
        apply hne
        have h3 : (restrictMap M hH).facePerm x = e₂ := isNextH_unique M hH hn h₂
        exact hx.trans (h3 ▸ ⟨1, by simp⟩)
  refine core_contra (eulerDefect_subRot M (plusEdge_le hH d))
    (SimpleGraph.Dart.symm_ne (newDart H d)).symm rfl hface ?_
  exact compSetoid_of_reach M (plusEdge_le hH d) (le_plusEdge H d) hconn (z := newDart H d) hnot hd hd'

/-- Adding a pendant edge `d` to `H` does not merge faces of `H`. -/
private theorem sameCycle_of_pendant (M : PlaneMap G) (hH : H ≤ G) {d : G.Dart}
    (hd : d.fst ∈ subVerts H) (hd' : d.snd ∉ subVerts H) {e₁ : H.Dart}
    (h₁ : IsNextH M hH d e₁) {x y : H.Dart}
    (hxy : SameCycle (restrictMap M (plusEdge_le hH d)).facePerm (toDart (le_plusEdge H d) x)
      (toDart (le_plusEdge H d) y)) :
    SameCycle (restrictMap M hH).facePerm x y := by
  have hnot : ¬ InH H d := fun h => hd' ⟨d.fst, h.symm⟩
  let g : (plusEdge H d).Dart → H.Dart := fun a =>
    if h : H.Adj a.fst a.snd then ⟨a.toProd, h⟩ else e₁
  have hg : ∀ x : H.Dart, g (toDart (le_plusEdge H d) x) = x := fun x => dite_eq_left x.adj
  have hgd : g (newDart H d) = e₁ := dite_eq_right hnot
  have hgd' : g (newDart H d).symm = e₁ := dite_eq_right fun h => hnot h.symm
  have key := sameCycle_of_step (Setoid.comap g (SameCycle.setoid (restrictMap M hH).facePerm))
    (π := (restrictMap M (plusEdge_le hH d)).facePerm) (fun a => ?_) hxy
  · rw [Setoid.comap_rel, hg, hg] at key
    exact key
  rw [Setoid.comap_rel]
  change SameCycle (restrictMap M hH).facePerm (g a)
    (g (subRot M (plusEdge_le hH d) a.symm))
  rcases dart_plusEdge_cases a with h | h | h
  · let x' : H.Dart := ⟨a.toProd, h⟩
    have hx' : a = toDart (le_plusEdge H d) x' := rfl
    rw [hx', hg, show (toDart (le_plusEdge H d) x').symm = toDart (le_plusEdge H d) x'.symm
      from rfl]
    rcases subRot_plusEdge_cases M hH d x'.symm with h1 | ⟨h1, hn⟩ | ⟨h1, -⟩
    · rw [h1, hg]
      exact ⟨1, rfl⟩
    · rw [h1, hgd, isNextH_unique M hH h₁ hn]
      exact ⟨1, rfl⟩
    · exfalso
      have hf := (isRotationSystem_subRot M (plusEdge_le hH d)).fst_apply
        (toDart (le_plusEdge H d) x'.symm)
      rw [h1] at hf
      exact hd' (by rw [show d.snd = x'.symm.fst from hf]; exact ⟨_, x'.symm.adj⟩)
  · rw [h, eq_symm_newDart hd' (subRot M (plusEdge_le hH d) (newDart H d).symm)
      (((isRotationSystem_subRot M (plusEdge_le hH d)).fst_apply _).trans rfl), hgd, hgd']
  · rw [h, SimpleGraph.Dart.symm_symm, subRot_newDart M hH hd hnot h₁, hgd', hg]

private theorem sameCycle_of_rIn_aux (M : PlaneMap G) (n : ℕ) :
    ∀ (H : SimpleGraph V) (hH : H ≤ G), (subVerts H)ᶜ.ncard = n →
    (∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b) →
    ∀ {d e : G.Dart}, d.fst ∈ subVerts H → e.fst ∈ subVerts H → d.snd ∉ subVerts H →
    e.snd ∉ subVerts H → RIn G (subVerts H)ᶜ d.snd e.snd → ∀ {e₁ e₂ : H.Dart},
    IsNextH M hH d e₁ → IsNextH M hH e e₂ → SameCycle (restrictMap M hH).facePerm e₁ e₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H hH hn hconn d e hd he hd' he' hde e₁ e₂ h₁ h₂
  by_cases hdeq : d = e
  · subst hdeq
    rw [isNextH_unique M hH h₁ h₂]
  have hsub : ∀ v, v ∈ subVerts (plusEdge H d) ↔ v ∈ subVerts H ∨ v = d.snd :=
    fun v => mem_subVerts_plusEdge hd
  have hconn' := reachable_plusEdge hd hconn
  have hnot : ¬ InH H d := fun h => hd' ⟨d.fst, h.symm⟩
  obtain ⟨e₂', he₂'⟩ := exists_isNextH M (plusEdge_le hH d) (d := e) ((hsub _).2 (Or.inl he))
  have hsymm : ∀ x : G.Dart, x.fst = d.snd →
      IsNextH M (plusEdge_le hH d) x (newDart H d).symm := by
    intro x hx
    obtain ⟨y, hy⟩ := exists_isNextH M (plusEdge_le hH d) (d := x) ((hsub _).2 (Or.inr hx))
    rwa [← eq_symm_newDart hd' y ((isNextH_fst M _ hy).trans hx)]
  have hmain : SameCycle (restrictMap M (plusEdge_le hH d)).facePerm (newDart H d).symm e₂' := by
    by_cases hsnd : d.snd = e.snd
    · have hnot' : ¬ InH (plusEdge H d) e := by
        intro h
        rcases plusEdge_adj.1 h with h | ⟨h1, h2⟩ | ⟨h1, -⟩
        · exact he' ⟨e.fst, h.symm⟩
        · exact hdeq (dart_eq_of h1.symm h2.symm)
        · exact hd' (h1 ▸ he)
      exact (sameCycle_of_chord_aux M (plusEdge_le hH d) hconn' ((hsub _).2 (Or.inl he))
        ((hsub _).2 (Or.inr hsnd.symm)) hnot' he₂' (hsymm e.symm hsnd.symm)).symm
    · obtain ⟨w, hw1, hw2, hw3, hw4⟩ := rIn_split hde hsnd
      have hset : (subVerts (plusEdge H d))ᶜ = (subVerts H)ᶜ \ {d.snd} := by
        ext v
        simp only [Set.mem_compl_iff, hsub, Set.mem_sdiff, Set.mem_singleton_iff, not_or]
      have hlt : (subVerts (plusEdge H d))ᶜ.ncard < n := by
        rw [hset, ← hn]
        exact Set.ncard_sdiff_singleton_lt_of_mem hd' (Set.toFinite _)
      refine ih _ hlt (plusEdge H d) (plusEdge_le hH d) rfl hconn'
        (d := ⟨(d.snd, w), hw1⟩) (e := e) ((hsub _).2 (Or.inr rfl)) ((hsub _).2 (Or.inl he))
        ?_ ?_ ?_ (hsymm _ rfl) he₂'
      · rw [hsub]
        rintro (h | h)
        · exact hw2 h
        · exact hw3 h
      · rw [hsub]
        rintro (h | h)
        · exact he' h
        · exact hsnd h.symm
      · rw [hset]
        exact hw4
  have hF1 := subRot_newDart M hH hd hnot h₁
  have hstart : SameCycle (restrictMap M (plusEdge_le hH d)).facePerm
      (toDart (le_plusEdge H d) e₁) e₂' :=
    (show SameCycle (restrictMap M (plusEdge_le hH d)).facePerm (newDart H d).symm
      (toDart (le_plusEdge H d) e₁) from ⟨1, by simp [PlaneMap.facePerm_apply, restrictMap, hF1]⟩).symm.trans hmain
  rcases dart_plusEdge_cases e₂' with h | h | h
  · let x : H.Dart := ⟨e₂'.toProd, h⟩
    have hx : e₂' = toDart (le_plusEdge H d) x := rfl
    have hex : IsNextH M hH e x :=
      isNextH_trans M hH (plusEdge_le hH d) (le_plusEdge H d) he₂' (isNextH_self M hH (d := toDart (plusEdge_le hH d) e₂') h)
    rw [isNextH_unique M hH h₂ hex]
    exact sameCycle_of_pendant M hH hd hd' h₁ (hx ▸ hstart)
  · have hex : IsNextH M hH e e₁ :=
      isNextH_trans M hH (plusEdge_le hH d) (le_plusEdge H d) he₂' (by rw [h]; exact h₁)
    rw [isNextH_unique M hH h₂ hex]
  · exfalso
    have hf := isNextH_fst M (plusEdge_le hH d) he₂'
    rw [h] at hf
    exact hd' (by rw [show d.snd = e.fst from hf]; exact he)

/-- **R1.** If `H` is connected, darts leading from `H` into the same component of `G - V(H)` lie
in gaps of the same face of `H`. -/
theorem sameCycle_of_rIn (M : PlaneMap G) (hH : H ≤ G)
    (hconn : ∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b)
    {d e : G.Dart} (hd : d.fst ∈ subVerts H) (he : e.fst ∈ subVerts H)
    (hd' : d.snd ∉ subVerts H) (he' : e.snd ∉ subVerts H)
    (hde : RIn G (subVerts H)ᶜ d.snd e.snd) {e₁ e₂ : H.Dart}
    (h₁ : IsNextH M hH d e₁) (h₂ : IsNextH M hH e e₂) :
    SameCycle (restrictMap M hH).facePerm e₁ e₂ := by
  exact sameCycle_of_rIn_aux M _ H hH rfl hconn hd he hd' he' hde h₁ h₂

/-- **R2.** If `H` is connected, both ends of a chord of `H` lie in gaps of the same face of `H`. -/
theorem sameCycle_of_chord (M : PlaneMap G) (hH : H ≤ G)
    (hconn : ∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b)
    {d : G.Dart} (hd : d.fst ∈ subVerts H) (hd' : d.snd ∈ subVerts H) (hnot : ¬ InH H d)
    {e₁ e₂ : H.Dart} (h₁ : IsNextH M hH d e₁) (h₂ : IsNextH M hH d.symm e₂) :
    SameCycle (restrictMap M hH).facePerm e₁ e₂ := by
  exact sameCycle_of_chord_aux M hH hconn hd hd' hnot h₁ h₂

/-- **R3.** If the face of `H` through `e` is also a face of `G`, its gaps are empty: a dart of `G`
whose next dart of `H` lies on that face is itself that dart of `H`. -/
theorem eq_of_isNextH_of_face (M : PlaneMap G) (hH : H ≤ G) {e : H.Dart}
    (hface : ∀ e', SameCycle (restrictMap M hH).facePerm e e' →
      M.facePerm (toDart hH e') = toDart hH ((restrictMap M hH).facePerm e'))
    {d : G.Dart} {e' : H.Dart} (he' : SameCycle (restrictMap M hH).facePerm e e')
    (hd : IsNextH M hH d e') : d = toDart hH e' := by
  obtain ⟨n, hn, hmin⟩ := hd
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simpa using hn
  · exfalso
    set f := (restrictMap M hH).facePerm with hf
    have hs : SameCycle f e (f⁻¹ e') := he'.trans ⟨-1, by simp⟩
    have h1 := hface (f⁻¹ e') hs
    rw [show f (f⁻¹ e') = e' from f.apply_symm_apply e', PlaneMap.facePerm_apply] at h1
    have h2 : (M.rot ^ (n - 1)) d = (toDart hH (f⁻¹ e')).symm := by
      apply M.rot.injective
      rw [h1, ← Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hpos, hn]
    exact hmin (n - 1) (by omega) (by rw [h2]; exact (f⁻¹ e').adj.symm)

end Grotzsch
