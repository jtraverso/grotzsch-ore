/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Planar.Colouring

/-!
# Adding a vertex inside a face of a plane map

Let `PM` be a plane map of `G` and `o` a dart whose face (the cycle of the face permutation
through `o`) visits every vertex at most once.  Then the graph obtained by adding a new vertex
adjacent to all vertices of that face is again planar (`isPlanar_apexExtend_face`).

The new rotation system is explicit: around a face vertex `e.fst` (for a face dart `e`) the new
dart towards the apex is inserted between the reverse of the previous face dart and `e`; around
the apex the new darts follow the face in reverse.  The face is replaced by `p` triangles.
Euler's defect does not increase (`eulerDefect_apex_le`): the dart count grows by `2p`, the
rotation gains one cycle (the apex), the edge involution gains `p` cycles, the face permutation
gains `p - 1` cycles, and no component is created.  The cycle counts are bounded below by
invariant functions (`le_cycleCount_of_invariant`, `le_cycleCount_add_one_of_invariant`) and the
component count above by a surjection of components (`numClasses_le_of_map`).

Consequently (`isK5Boundary_face`) the vertex set of such a face is a `K_5`-minor-free boundary
of `G` in the sense of Wood–Linusson: this is the only topological input needed for Li–Wang's
Theorem 3.1.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

open Equiv Equiv.Perm

/-! ### Counting tools -/

section Counting

variable {α : Type*}

/-- A function constant on the cycles of `π` and onto `Q` bounds the cycle count below. -/
theorem le_cycleCount_of_invariant [Finite α] {π : Perm α} {Q : Type*} (g : α → Q)
    (hg : ∀ x, g (π x) = g x) (hsurj : Function.Surjective g) : Nat.card Q ≤ cycleCount π := by
  unfold cycleCount numClasses
  refine Nat.card_le_card_of_surjective
    (Quotient.lift g (fun a b h => sameCycle_of_step (Setoid.ker g)
      (fun z => (hg z).symm) h)) ?_
  intro q
  obtain ⟨x, rfl⟩ := hsurj q
  exact ⟨Quotient.mk _ x, rfl⟩

/-- A function constant on the cycles of `π` whose range misses at most `q₀`. -/
theorem le_cycleCount_add_one_of_invariant [Finite α] {π : Perm α} {Q : Type*} (g : α → Q)
    (hg : ∀ x, g (π x) = g x) (q₀ : Q) (hsurj : ∀ q, q ≠ q₀ → ∃ x, g x = q) :
    Nat.card Q ≤ cycleCount π + 1 := by
  classical
  unfold cycleCount numClasses
  rw [← Finite.card_option]
  refine Nat.card_le_card_of_surjective (fun o => match o with
    | none => q₀
    | some c => Quotient.lift g (fun a b h => sameCycle_of_step (Setoid.ker g)
      (fun z => (hg z).symm) h) c) ?_
  intro q
  by_cases hq : q = q₀
  · exact ⟨none, hq.symm⟩
  · obtain ⟨x, rfl⟩ := hsurj q hq
    exact ⟨some (Quotient.mk _ x), rfl⟩

/-- Components: a relation-preserving map hitting every class bounds the class count. -/
theorem numClasses_le_of_map [Finite α] {β : Type*} {s : Setoid α} {t : Setoid β}
    (h : α → β) (hst : ∀ a b, s a b → t (h a) (h b)) (hsurj : ∀ y, ∃ x, t (h x) y) :
    numClasses t ≤ numClasses s := by
  unfold numClasses
  refine Nat.card_le_card_of_surjective (Quotient.map h hst) ?_
  intro q
  induction q using Quotient.inductionOn with
  | h y =>
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨Quotient.mk _ x, Quotient.sound hx⟩

end Counting

/-! ### The construction -/

namespace FaceApex

variable {V : Type*} {G : SimpleGraph V} (PM : PlaneMap G) (o : G.Dart)

/-- The darts of the face through `o`. -/
abbrev F := {d : G.Dart // SameCycle PM.facePerm o d}

/-- The darts of the new map: the old darts, and for each face dart `e` a dart from `e.fst` to
the apex (`true`) and its reverse (`false`). -/
abbrev D := G.Dart ⊕ (F PM o × Bool)

variable {PM o}

theorem facePerm_symm (d : G.Dart) : PM.facePerm d.symm = PM.rot d := by
  rw [PlaneMap.facePerm_apply, SimpleGraph.Dart.symm_symm]

theorem mem_F_rot_iff (d : G.Dart) :
    SameCycle PM.facePerm o (PM.rot d) ↔ SameCycle PM.facePerm o d.symm := by
  rw [← facePerm_symm, sameCycle_apply_right]

theorem mem_F_rot_inv_symm_iff (d : G.Dart) :
    SameCycle PM.facePerm o (PM.rot⁻¹ d).symm ↔ SameCycle PM.facePerm o d := by
  rw [← sameCycle_apply_right, facePerm_symm]
  simp

variable (PM o)

/-- The next face dart. -/
def faceNext (e : F PM o) : F PM o := ⟨PM.facePerm e.1, sameCycle_apply_right.2 e.2⟩

/-- The previous face dart. -/
def facePrev (e : F PM o) : F PM o :=
  ⟨PM.facePerm⁻¹ e.1, sameCycle_apply_right.1 (by simpa using e.2)⟩

theorem faceNext_facePrev (e : F PM o) : faceNext PM o (facePrev PM o e) = e :=
  Subtype.ext (by simp [faceNext, facePrev])

theorem facePrev_faceNext (e : F PM o) : facePrev PM o (faceNext PM o e) = e :=
  Subtype.ext (by simp [faceNext, facePrev])

/-- The new edge involution. -/
def alphaFun : D PM o → D PM o
  | .inl d => .inl d.symm
  | .inr (e, b) => .inr (e, !b)

theorem alphaFun_involutive : Function.Involutive (alphaFun PM o) := by
  rintro (d | ⟨e, b⟩) <;> simp [alphaFun]

/-- The new edge involution, as a permutation. -/
def alpha' : Perm (D PM o) := (alphaFun_involutive PM o).toPerm _

open Classical in
/-- The new rotation. -/
noncomputable def sigmaFun : D PM o → D PM o
  | .inl d => if h : SameCycle PM.facePerm o d.symm then
      .inr (⟨PM.rot d, (mem_F_rot_iff d).2 h⟩, true) else .inl (PM.rot d)
  | .inr (e, true) => .inl e.1
  | .inr (e, false) => .inr (facePrev PM o e, false)

open Classical in
/-- The inverse of the new rotation. -/
noncomputable def sigmaInvFun : D PM o → D PM o
  | .inl d => if h : SameCycle PM.facePerm o d then .inr (⟨d, h⟩, true) else .inl (PM.rot⁻¹ d)
  | .inr (e, true) => .inl (PM.rot⁻¹ e.1)
  | .inr (e, false) => .inr (faceNext PM o e, false)

theorem sigmaInv_sigma (x : D PM o) : sigmaInvFun PM o (sigmaFun PM o x) = x := by
  rcases x with d | ⟨e, _ | _⟩
  · by_cases h : SameCycle PM.facePerm o d.symm
    · simp [sigmaFun, sigmaInvFun, h]
    · have h' : ¬ SameCycle PM.facePerm o (PM.rot d) := fun h' => h ((mem_F_rot_iff d).1 h')
      simp [sigmaFun, sigmaInvFun, h, h']
  · simp [sigmaFun, sigmaInvFun, faceNext_facePrev]
  · simp [sigmaFun, sigmaInvFun, e.2]

theorem sigma_sigmaInv (x : D PM o) : sigmaFun PM o (sigmaInvFun PM o x) = x := by
  rcases x with d | ⟨e, _ | _⟩
  · by_cases h : SameCycle PM.facePerm o d
    · simp [sigmaFun, sigmaInvFun, h]
    · have h' : ¬ SameCycle PM.facePerm o (PM.rot⁻¹ d).symm :=
        fun h' => h ((mem_F_rot_inv_symm_iff d).1 h')
      simp only [sigmaInvFun, h, ↓reduceDIte, sigmaFun, h']
      simp
  · simp [sigmaFun, sigmaInvFun, facePrev_faceNext]
  · have h : SameCycle PM.facePerm o (PM.rot⁻¹ e.1).symm := (mem_F_rot_inv_symm_iff _).2 e.2
    simp only [sigmaInvFun, sigmaFun, h, ↓reduceDIte]
    simp

/-- The new rotation, as a permutation. -/
noncomputable def sigma' : Perm (D PM o) :=
  ⟨sigmaFun PM o, sigmaInvFun PM o, sigmaInv_sigma PM o, sigma_sigmaInv PM o⟩

theorem sigma'_inl_of_mem {d : G.Dart} (h : SameCycle PM.facePerm o d.symm) :
    sigma' PM o (.inl d) = .inr (⟨PM.rot d, (mem_F_rot_iff d).2 h⟩, true) := by
  simp [sigma', sigmaFun, h]

theorem sigma'_inl_of_not_mem {d : G.Dart} (h : ¬ SameCycle PM.facePerm o d.symm) :
    sigma' PM o (.inl d) = .inl (PM.rot d) := by
  simp [sigma', sigmaFun, h]

@[simp] theorem sigma'_out (e : F PM o) : sigma' PM o (.inr (e, true)) = .inl e.1 := rfl

@[simp] theorem sigma'_in (e : F PM o) :
    sigma' PM o (.inr (e, false)) = .inr (facePrev PM o e, false) := rfl

@[simp] theorem alpha'_inl (d : G.Dart) : alpha' PM o (.inl d) = .inl d.symm := rfl

@[simp] theorem alpha'_inr (e : F PM o) (b : Bool) : alpha' PM o (.inr (e, b)) = .inr (e, !b) :=
  rfl

/-! ### Cycle counts and components -/

section Counts

variable [Finite V]

instance finite_dart : Finite G.Dart := by
  classical
  have := Fintype.ofFinite V
  infer_instance

theorem card_D : Nat.card (D PM o) = Nat.card G.Dart + 2 * Nat.card (F PM o) := by
  rw [Nat.card_sum, Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
  ring

theorem cycleCount_alpha'_ge :
    cycleCount (dartSymm G) + Nat.card (F PM o) ≤ cycleCount (alpha' PM o) := by
  suffices key : Nat.card (Quotient (SameCycle.setoid (dartSymm G)) ⊕ F PM o) ≤
      cycleCount (alpha' PM o) by
    rw [Nat.card_sum] at key; exact key
  refine le_cycleCount_of_invariant
    (fun x => match x with
      | .inl d => Sum.inl (Quotient.mk (SameCycle.setoid (dartSymm G)) d)
      | .inr (e, _) => Sum.inr e) (fun x => ?_) ?_
  · rcases x with d | ⟨e, b⟩
    · simp only [alpha'_inl, Sum.inl.injEq]
      apply Quotient.sound
      change SameCycle _ _ _
      exact (sameCycle_dartSymm_iff G).2 (Or.inr rfl) |>.symm
    · rfl
  · rintro (q | e)
    · induction q using Quotient.inductionOn with
      | h d => exact ⟨.inl d, rfl⟩
    · exact ⟨.inr (e, true), rfl⟩

theorem cycleCount_sigma'_ge : cycleCount PM.rot + 1 ≤ cycleCount (sigma' PM o) := by
  suffices key : Nat.card (Option (Quotient (SameCycle.setoid PM.rot))) ≤
      cycleCount (sigma' PM o) by
    rw [Finite.card_option] at key; exact key
  refine le_cycleCount_of_invariant
    (fun x => match x with
      | .inl d => some (Quotient.mk (SameCycle.setoid PM.rot) d)
      | .inr (e, true) => some (Quotient.mk (SameCycle.setoid PM.rot) e.1)
      | .inr (_, false) => none) (fun x => ?_) ?_
  · rcases x with d | ⟨e, _ | _⟩
    · by_cases h : SameCycle PM.facePerm o d.symm
      · rw [sigma'_inl_of_mem PM o h]
        simp only [Option.some.injEq]
        exact Quotient.sound (show SameCycle _ _ _ from ⟨1, by simp⟩).symm
      · rw [sigma'_inl_of_not_mem PM o h]
        simp only [Option.some.injEq]
        exact Quotient.sound (show SameCycle _ _ _ from ⟨1, by simp⟩).symm
    · rfl
    · rfl
  · rintro (_ | q)
    · exact ⟨.inr (⟨o, SameCycle.refl _ _⟩, false), rfl⟩
    · induction q using Quotient.inductionOn with
      | h d => exact ⟨.inl d, rfl⟩

omit [Finite V] in
open Classical in
theorem mul_inl (d : G.Dart) : (sigma' PM o * alpha' PM o) (.inl d) =
    if h : SameCycle PM.facePerm o d then
      .inr (⟨PM.facePerm d, sameCycle_apply_right.2 h⟩, true)
    else .inl (PM.facePerm d) := by
  rw [Perm.mul_apply, alpha'_inl]
  by_cases h : SameCycle PM.facePerm o d
  · have h' : SameCycle PM.facePerm o d.symm.symm := by simpa using h
    rw [sigma'_inl_of_mem PM o h']
    simp only [h, ↓reduceDIte]
    rfl
  · have h' : ¬ SameCycle PM.facePerm o d.symm.symm := by simpa using h
    rw [sigma'_inl_of_not_mem PM o h']
    simp only [h, ↓reduceDIte]
    rfl

theorem cycleCount_face_ge :
    cycleCount PM.facePerm + Nat.card (F PM o) ≤ cycleCount (sigma' PM o * alpha' PM o) + 1 := by
  classical
  suffices key : Nat.card (Quotient (SameCycle.setoid PM.facePerm) ⊕ F PM o) ≤
      cycleCount (sigma' PM o * alpha' PM o) + 1 by
    rw [Nat.card_sum] at key; exact key
  refine le_cycleCount_add_one_of_invariant
    (fun x => match x with
      | .inl d => if h : SameCycle PM.facePerm o d then Sum.inr ⟨d, h⟩
          else Sum.inl (Quotient.mk (SameCycle.setoid PM.facePerm) d)
      | .inr (e, true) => Sum.inr (facePrev PM o e)
      | .inr (e, false) => Sum.inr e) (fun x => ?_)
    (Sum.inl (Quotient.mk (SameCycle.setoid PM.facePerm) o)) ?_
  · rcases x with d | ⟨e, _ | _⟩
    · rw [mul_inl]
      by_cases h : SameCycle PM.facePerm o d
      · simp only [h, ↓reduceDIte]
        exact congrArg Sum.inr (Subtype.ext (by simp [facePrev]))
      · have h' : ¬ SameCycle PM.facePerm o (PM.facePerm d) := fun h' =>
          h (sameCycle_apply_right.1 h')
        simp only [h, h', ↓reduceDIte, Sum.inl.injEq]
        exact Quotient.sound (show SameCycle _ _ _ from ⟨1, by simp⟩).symm
    · simp [Perm.mul_apply, e.2]
    · simp [Perm.mul_apply]
  · rintro (q | e) hq
    · induction q using Quotient.inductionOn with
      | h d =>
        have h : ¬ SameCycle PM.facePerm o d := fun h => hq (congrArg Sum.inl
          (Quotient.sound h.symm))
        exact ⟨.inl d, by simp [h]⟩
    · exact ⟨.inr (e, false), rfl⟩

theorem numComponents_le :
    numComponents (sigma' PM o) (alpha' PM o) ≤ numComponents PM.rot (dartSymm G) := by
  refine numClasses_le_of_map (fun d => (Sum.inl d : D PM o)) (fun a b hab => ?_) ?_
  · refine compSetoid_le (Setoid.comap (fun d => (Sum.inl d : D PM o))
      (compSetoid (sigma' PM o) (alpha' PM o))) (fun z => ?_) (fun z => ?_) hab
    · rw [Setoid.comap_rel]
      by_cases h : SameCycle PM.facePerm o z.symm
      · have h1 := compSetoid_left (sigma' PM o) (alpha' PM o) (.inl z)
        rw [sigma'_inl_of_mem PM o h] at h1
        have h2 := compSetoid_left (sigma' PM o) (alpha' PM o)
          (.inr (⟨PM.rot z, (mem_F_rot_iff z).2 h⟩, true))
        rw [sigma'_out] at h2
        exact (compSetoid _ _).trans h1 h2
      · have h1 := compSetoid_left (sigma' PM o) (alpha' PM o) (.inl z)
        rw [sigma'_inl_of_not_mem PM o h] at h1
        exact h1
    · rw [Setoid.comap_rel]
      exact compSetoid_right (sigma' PM o) (alpha' PM o) (.inl z)
  · rintro (d | ⟨e, _ | _⟩)
    · exact ⟨d, (compSetoid _ _).refl _⟩
    · have h1 := compSetoid_right (sigma' PM o) (alpha' PM o) (.inr (e, false))
      have h2 := compSetoid_left (sigma' PM o) (alpha' PM o) (.inr (e, true))
      rw [alpha'_inr, Bool.not_false] at h1
      rw [sigma'_out] at h2
      exact ⟨e.1, (compSetoid _ _).symm ((compSetoid _ _).trans h1 h2)⟩
    · have h2 := compSetoid_left (sigma' PM o) (alpha' PM o) (.inr (e, true))
      rw [sigma'_out] at h2
      exact ⟨e.1, (compSetoid _ _).symm h2⟩

/-- **Adding an apex inside a face does not increase the Euler defect.** -/
theorem eulerDefect_apex_le :
    eulerDefect (sigma' PM o) (alpha' PM o) ≤ eulerDefect PM.rot (dartSymm G) := by
  have h1 := card_D (PM := PM) (o := o)
  have h2 := cycleCount_alpha'_ge (PM := PM) (o := o)
  have h3 := cycleCount_sigma'_ge (PM := PM) (o := o)
  have h4 := cycleCount_face_ge (PM := PM) (o := o)
  have h5 := numComponents_le (PM := PM) (o := o)
  have h6 : cycleCount (PM.rot * dartSymm G) = cycleCount PM.facePerm := rfl
  unfold eulerDefect
  rw [h6]
  omega

end Counts

/-! ### Transport to the apex graph -/

section Transport

/-- The vertices of the face through `o`. -/
def faceVerts : Set V := {v | ∃ e : F PM o, e.1.fst = v}

/-- The face dart leaving a face vertex. -/
noncomputable def faceDartAt {v : V} (h : v ∈ faceVerts PM o) : F PM o := Classical.choose h

theorem faceDartAt_fst {v : V} (h : v ∈ faceVerts PM o) : (faceDartAt PM o h).1.fst = v :=
  Classical.choose_spec h

variable {PM o}

theorem mem_faceVerts (e : F PM o) : e.1.fst ∈ faceVerts PM o := ⟨e, rfl⟩

variable (PM o)

/-- The darts of the apex graph `apexExtend G (faceVerts PM o)`, from the abstract darts. -/
def toDart : D PM o → (apexExtend G (faceVerts PM o)).Dart
  | .inl d => ⟨(some d.fst, some d.snd), d.adj⟩
  | .inr (e, true) => ⟨(some e.1.fst, none), mem_faceVerts e⟩
  | .inr (e, false) => ⟨(none, some e.1.fst), mem_faceVerts e⟩

/-- The inverse of `toDart`. -/
noncomputable def ofDart : (apexExtend G (faceVerts PM o)).Dart → D PM o
  | ⟨(some a, some b), h⟩ => .inl ⟨(a, b), h⟩
  | ⟨(some _, none), h⟩ => .inr (faceDartAt PM o h, true)
  | ⟨(none, some _), h⟩ => .inr (faceDartAt PM o h, false)
  | ⟨(none, none), h⟩ => absurd h (apexExtend_none_none)

variable {PM o}

theorem ofDart_toDart (hinj : ∀ e e' : F PM o, e.1.fst = e'.1.fst → e = e') (x : D PM o) :
    ofDart PM o (toDart PM o x) = x := by
  rcases x with d | ⟨e, _ | _⟩
  · rfl
  · exact congrArg (fun e => Sum.inr (e, false)) (hinj _ _ (faceDartAt_fst PM o _))
  · exact congrArg (fun e => Sum.inr (e, true)) (hinj _ _ (faceDartAt_fst PM o _))

theorem toDart_ofDart (y : (apexExtend G (faceVerts PM o)).Dart) :
    toDart PM o (ofDart PM o y) = y := by
  rcases y with ⟨⟨_ | a, _ | b⟩, h⟩
  · exact absurd h (apexExtend_none_none)
  · refine (SimpleGraph.Dart.ext_iff _ _).2 ?_
    exact Prod.ext rfl (congrArg some (faceDartAt_fst PM o (show b ∈ faceVerts PM o from h)))
  · refine (SimpleGraph.Dart.ext_iff _ _).2 ?_
    exact Prod.ext (congrArg some (faceDartAt_fst PM o (show a ∈ faceVerts PM o from h))) rfl
  · rfl

/-- The relabelling of darts. -/
noncomputable def dartEquiv (hinj : ∀ e e' : F PM o, e.1.fst = e'.1.fst → e = e') :
    D PM o ≃ (apexExtend G (faceVerts PM o)).Dart :=
  ⟨toDart PM o, ofDart PM o, ofDart_toDart hinj, toDart_ofDart⟩

theorem toDart_alpha' (x : D PM o) : toDart PM o (alpha' PM o x) = (toDart PM o x).symm := by
  rcases x with d | ⟨e, _ | _⟩ <;> rfl

theorem fst_toDart_sigma' (x : D PM o) :
    (toDart PM o (sigma' PM o x)).fst = (toDart PM o x).fst := by
  rcases x with d | ⟨e, _ | _⟩
  · by_cases h : SameCycle PM.facePerm o d.symm
    · rw [sigma'_inl_of_mem PM o h]
      simp [toDart, PM.isRotationSystem.fst_apply]
    · rw [sigma'_inl_of_not_mem PM o h]
      simp [toDart, PM.isRotationSystem.fst_apply]
  · rfl
  · rfl

theorem sameCycle_sigma'_inl_rot (d : G.Dart) :
    SameCycle (sigma' PM o) (.inl d) (.inl (PM.rot d)) := by
  by_cases h : SameCycle PM.facePerm o d.symm
  · refine ⟨2, ?_⟩
    simp only [zpow_ofNat, pow_two, Perm.mul_apply]
    rw [sigma'_inl_of_mem PM o h, sigma'_out]
  · exact ⟨1, by simp [sigma'_inl_of_not_mem PM o h]⟩

theorem sameCycle_sigma'_inl_pow (d : G.Dart) (k : ℕ) :
    SameCycle (sigma' PM o) (.inl d) (.inl ((PM.rot ^ k) d)) := by
  induction k with
  | zero => exact SameCycle.refl _ _
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans (sameCycle_sigma'_inl_rot _)

theorem sameCycle_sigma'_inl [Finite V] {d d' : G.Dart} (h : d.fst = d'.fst) :
    SameCycle (sigma' PM o) (.inl d) (.inl d') := by
  obtain ⟨k, hk⟩ := (PM.isRotationSystem.sameCycle d d' h).exists_nat_pow_eq
  rw [← hk]
  exact sameCycle_sigma'_inl_pow d k

theorem sameCycle_sigma'_out (e : F PM o) :
    SameCycle (sigma' PM o) (.inr (e, true)) (.inl e.1) := ⟨1, by simp⟩

theorem sameCycle_sigma'_in_next (e : F PM o) :
    SameCycle (sigma' PM o) (.inr (faceNext PM o e, false)) (.inr (e, false)) :=
  ⟨1, by simp [facePrev_faceNext]⟩

theorem faceNext_iterate_val (e : F PM o) (k : ℕ) :
    ((faceNext PM o)^[k] e).1 = (PM.facePerm ^ k) e.1 := by
  induction k generalizing e with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', Perm.mul_apply, ← ih]
    rfl

theorem sameCycle_sigma'_in [Finite V] (e e' : F PM o) :
    SameCycle (sigma' PM o) (.inr (e, false)) (.inr (e', false)) := by
  have hk : ∀ k : ℕ, SameCycle (sigma' PM o) (.inr (e, false))
      (.inr ((faceNext PM o)^[k] e, false)) := by
    intro k
    induction k with
    | zero => exact SameCycle.refl _ _
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (sameCycle_sigma'_in_next _).symm
  have hF : SameCycle PM.facePerm e.1 e'.1 := e.2.symm.trans e'.2
  obtain ⟨k, hk'⟩ := hF.exists_nat_pow_eq
  have : (faceNext PM o)^[k] e = e' := Subtype.ext (by rw [faceNext_iterate_val, hk'])
  rw [← this]
  exact hk k

theorem sameCycle_sigma'_of_fst [Finite V] {x y : D PM o}
    (h : (toDart PM o x).fst = (toDart PM o y).fst) : SameCycle (sigma' PM o) x y := by
  rcases x with d | ⟨e, _ | _⟩ <;> rcases y with d' | ⟨e', _ | _⟩ <;>
    simp only [toDart, Option.some.injEq, reduceCtorEq] at h
  · exact sameCycle_sigma'_inl h
  · exact (sameCycle_sigma'_inl h).trans (sameCycle_sigma'_out e').symm
  · exact sameCycle_sigma'_in e e'
  · exact (sameCycle_sigma'_out e).trans (sameCycle_sigma'_inl h)
  · exact (sameCycle_sigma'_out e).trans ((sameCycle_sigma'_inl h).trans
      (sameCycle_sigma'_out e').symm)

end Transport

end FaceApex

open FaceApex in
/-- **Adding a vertex inside a face.**  If the face of the plane map `PM` through the dart `o`
visits every vertex at most once, the graph obtained from `G` by adding a new vertex adjacent
to all vertices of that face is planar. -/
theorem isPlanar_apexExtend_face [Finite V] {G : SimpleGraph V} (PM : PlaneMap G) (o : G.Dart)
    (hinj : ∀ e e' : F PM o, e.1.fst = e'.1.fst → e = e') :
    IsPlanar (apexExtend G (faceVerts PM o)) := by
  set E := dartEquiv hinj with hE
  have hα : dartSymm (apexExtend G (faceVerts PM o)) = E.permCongr (alpha' PM o) := by
    refine Equiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := E.surjective y
    rw [dartSymm_apply, permCongr_apply, symm_apply_apply]
    exact (toDart_alpha' x).symm
  refine ⟨⟨E.permCongr (sigma' PM o), ⟨fun y => ?_, fun y y' hyy' => ?_⟩, ?_⟩⟩
  · obtain ⟨x, rfl⟩ := E.surjective y
    simp only [permCongr_apply, symm_apply_apply]
    exact fst_toDart_sigma' x
  · obtain ⟨x, rfl⟩ := E.surjective y
    obtain ⟨x', rfl⟩ := E.surjective y'
    exact (sameCycle_permCongr_iff E (sigma' PM o) x x').1 (sameCycle_sigma'_of_fst hyy')
  · rw [hα, eulerDefect_permCongr]
    exact le_antisymm ((eulerDefect_apex_le (PM := PM) (o := o)).trans PM.eulerDefect_eq_zero.le)
      (eulerDefect_nonneg _ _)

open FaceApex in
/-- **The vertices of a simple face form a `K_5`-minor-free boundary**: if the face of a plane
map through `o` visits every vertex at most once, then adding an apex adjacent to its vertices
creates no `K_5` minor. -/
theorem isK5Boundary_face [Finite V] {G : SimpleGraph V} (PM : PlaneMap G) (o : G.Dart)
    (hinj : ∀ e e' : F PM o, e.1.fst = e'.1.fst → e = e') :
    IsK5Boundary G (faceVerts PM o) :=
  cliqueMinorFree_five_of_isPlanar (isPlanar_apexExtend_face PM o hinj)

end LeanPool.K5MinorFreeChoosability
