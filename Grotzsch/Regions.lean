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

theorem subRotInvFun_subRotFun (M : PlaneMap G) (hH : H ≤ G) (d : H.Dart) :
    subRotInvFun M hH (subRotFun M hH d) = d := by
  sorry

theorem subRotFun_subRotInvFun (M : PlaneMap G) (hH : H ≤ G) (d : H.Dart) :
    subRotFun M hH (subRotInvFun M hH d) = d := by
  sorry

/-- The rotation induced on a subgraph. -/
def subRot (M : PlaneMap G) (hH : H ≤ G) : Perm H.Dart where
  toFun := subRotFun M hH
  invFun := subRotInvFun M hH
  left_inv := subRotInvFun_subRotFun M hH
  right_inv := subRotFun_subRotInvFun M hH

theorem subRot_apply (M : PlaneMap G) (hH : H ≤ G) (d : H.Dart) :
    toDart hH (subRot M hH d) = (M.rot ^ Nat.find (exists_rot_pow_inH M hH d)) (toDart hH d) :=
  rfl

theorem isRotationSystem_subRot (M : PlaneMap G) (hH : H ≤ G) :
    IsRotationSystem H (subRot M hH) := by
  sorry

/-- **J0.** The induced rotation of a subgraph of a plane map has Euler defect zero. -/
theorem eulerDefect_subRot (M : PlaneMap G) (hH : H ≤ G) :
    eulerDefect (subRot M hH) (dartSymm H) = 0 := by
  sorry

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
  sorry

theorem isNextH_unique (M : PlaneMap G) (hH : H ≤ G) {d : G.Dart} {e e' : H.Dart}
    (he : IsNextH M hH d e) (he' : IsNextH M hH d e') : e = e' := by
  sorry

/-- **R1.** If `H` is connected, darts leading from `H` into the same component of `G - V(H)` lie
in gaps of the same face of `H`. -/
theorem sameCycle_of_rIn (M : PlaneMap G) (hH : H ≤ G)
    (hconn : ∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b)
    {d e : G.Dart} (hd : d.fst ∈ subVerts H) (he : e.fst ∈ subVerts H)
    (hd' : d.snd ∉ subVerts H) (he' : e.snd ∉ subVerts H)
    (hde : RIn G (subVerts H)ᶜ d.snd e.snd) {e₁ e₂ : H.Dart}
    (h₁ : IsNextH M hH d e₁) (h₂ : IsNextH M hH e e₂) :
    SameCycle (restrictMap M hH).facePerm e₁ e₂ := by
  sorry

/-- **R2.** If `H` is connected, both ends of a chord of `H` lie in gaps of the same face of `H`. -/
theorem sameCycle_of_chord (M : PlaneMap G) (hH : H ≤ G)
    (hconn : ∀ a ∈ subVerts H, ∀ b ∈ subVerts H, H.Reachable a b)
    {d : G.Dart} (hd : d.fst ∈ subVerts H) (hd' : d.snd ∈ subVerts H) (hnot : ¬ InH H d)
    {e₁ e₂ : H.Dart} (h₁ : IsNextH M hH d e₁) (h₂ : IsNextH M hH d.symm e₂) :
    SameCycle (restrictMap M hH).facePerm e₁ e₂ := by
  sorry

/-- **R3.** If the face of `H` through `e` is also a face of `G`, its gaps are empty: a dart of `G`
whose next dart of `H` lies on that face is itself that dart of `H`. -/
theorem eq_of_isNextH_of_face (M : PlaneMap G) (hH : H ≤ G) {e : H.Dart}
    (hface : ∀ e', SameCycle (restrictMap M hH).facePerm e e' →
      M.facePerm (toDart hH e') = toDart hH ((restrictMap M hH).facePerm e'))
    {d : G.Dart} {e' : H.Dart} (he' : SameCycle (restrictMap M hH).facePerm e e')
    (hd : IsNextH M hH d e') : d = toDart hH e' := by
  sorry

end Grotzsch
