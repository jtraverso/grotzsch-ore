/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Planar.Nonplanar
public import LeanPool.K5MinorFreeChoosability.Planar.Examples

/-!
# Dart bounds for plane graphs without `K₂` components

For a finite plane graph in which every edge has an endpoint of degree at least two (i.e. there
is no component equal to a single edge), every face of the rotation system has length at least
three, and at least four if the graph is triangle-free.  With Euler's formula this gives

* `card_dart_add_twelve_le`: `|darts| + 12 ≤ 6 n'`, i.e. `e ≤ 3 n' - 6`;
* `card_dart_add_eight_le_of_cliqueFree`: `|darts| + 8 ≤ 4 n'` (triangle-free), i.e.
  `e ≤ 2 n' - 4`,

where `n'` is the number of non-isolated vertices.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

open Equiv Equiv.Perm

variable {V : Type*} {G : SimpleGraph V}

section Faces

variable {σ : Perm G.Dart} (hσ : IsRotationSystem G σ)
include hσ

/-- A face of length two lives in a component that is a single edge. -/
theorem face_face_ne_self_of_edge [Finite V]
    (hedge : ∀ d : G.Dart, 2 ≤ Nat.card {u // G.Adj d.fst u} ∨
      2 ≤ Nat.card {u // G.Adj d.snd u})
    (d : G.Dart) : (σ * dartSymm G) ((σ * dartSymm G) d) ≠ d := by
  intro h
  set e := (σ * dartSymm G) d with he
  have h1 : e.fst = d.snd := facePerm_fst hσ d
  have h2 : e.snd = d.fst := by
    have := facePerm_fst hσ e
    rw [h] at this
    exact this.symm
  have hed : e = d.symm := SimpleGraph.Dart.ext_iff _ _ |>.2 (Prod.ext h1 h2)
  have hfix1 : σ d.symm = d.symm := by
    have : (σ * dartSymm G) d = σ d.symm := rfl
    rw [← this, ← he, hed]
  have hfix2 : σ d = d := by
    have : (σ * dartSymm G) e = σ e.symm := rfl
    rw [h, hed, SimpleGraph.Dart.symm_symm] at this
    exact this.symm
  have hone : ∀ (x : G.Dart), σ x = x → Nat.card {u // G.Adj x.fst u} ≤ 1 := by
    intro x hx
    have hall : ∀ u (hu : G.Adj x.fst u), (⟨(x.fst, u), hu⟩ : G.Dart) = x := by
      intro u hu
      exact ((hσ.sameCycle x ⟨(x.fst, u), hu⟩ rfl).eq_of_left hx).symm
    refine Finite.card_le_one_iff_subsingleton.2 ⟨fun a b => ?_⟩
    have k1 := hall a.1 a.2
    have k2 := hall b.1 b.2
    exact Subtype.ext (congrArg (fun e : G.Dart => e.snd) (k1.trans k2.symm))
  have a1 := hone d hfix2
  have a2 := hone d.symm hfix1
  change Nat.card {u // G.Adj d.snd u} ≤ 1 at a2
  rcases hedge d with h | h <;> omega

theorem face_three_ne_self_of_cliqueFree (hG : G.CliqueFree 3) (d : G.Dart) :
    (σ * dartSymm G) ((σ * dartSymm G) ((σ * dartSymm G) d)) ≠ d := by
  classical
  intro h
  set φ := σ * dartSymm G
  have e1 : (φ d).fst = d.snd := facePerm_fst hσ d
  have e2 : (φ (φ d)).fst = (φ d).snd := facePerm_fst hσ (φ d)
  have e3 : d.fst = (φ (φ d)).snd := by
    have := facePerm_fst hσ (φ (φ d))
    rw [h] at this
    exact this
  have ab : G.Adj d.fst d.snd := d.adj
  have bc : G.Adj d.snd (φ d).snd := e1 ▸ (φ d).adj
  have ca : G.Adj (φ d).snd d.fst := by
    have := (φ (φ d)).adj
    rw [e2, ← e3] at this
    exact this
  apply hG {d.fst, d.snd, (φ d).snd}
  rw [SimpleGraph.is3Clique_triple_iff]
  exact ⟨ab, ca.symm, bc⟩

theorem three_le_card_face_of_edge [Finite V]
    (hedge : ∀ d : G.Dart, 2 ≤ Nat.card {u // G.Adj d.fst u} ∨
      2 ≤ Nat.card {u // G.Adj d.snd u})
    (d : G.Dart) : 3 ≤ Nat.card {e // SameCycle (σ * dartSymm G) d e} := by
  classical
  have := Fintype.ofFinite V
  set φ := σ * dartSymm G
  have n1 : φ d ≠ d := face_ne_self hσ d
  have n2 : φ (φ d) ≠ d := face_face_ne_self_of_edge hσ hedge d
  have n3 : φ (φ d) ≠ φ d := face_ne_self hσ (φ d)
  refine le_natCard_of_list [d, φ d, φ (φ d)] ?_ ?_
  · simp [Ne.symm n1, Ne.symm n2, Ne.symm n3]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact SameCycle.refl _ _
    · exact sameCycle_apply_right.2 (SameCycle.refl _ _)
    · exact sameCycle_apply_right.2 (sameCycle_apply_right.2 (SameCycle.refl _ _))

theorem four_le_card_face_of_cliqueFree [Finite V] (hG : G.CliqueFree 3)
    (hedge : ∀ d : G.Dart, 2 ≤ Nat.card {u // G.Adj d.fst u} ∨
      2 ≤ Nat.card {u // G.Adj d.snd u})
    (d : G.Dart) : 4 ≤ Nat.card {e // SameCycle (σ * dartSymm G) d e} := by
  classical
  have := Fintype.ofFinite V
  set φ := σ * dartSymm G
  have n1 : φ d ≠ d := face_ne_self hσ d
  have n2 : φ (φ d) ≠ d := face_face_ne_self_of_edge hσ hedge d
  have n3 : φ (φ (φ d)) ≠ d := face_three_ne_self_of_cliqueFree hσ hG d
  have m1 : φ (φ d) ≠ φ d := face_ne_self hσ (φ d)
  have m2 : φ (φ (φ d)) ≠ φ d := face_face_ne_self_of_edge hσ hedge (φ d)
  have m3 : φ (φ (φ d)) ≠ φ (φ d) := face_ne_self hσ (φ (φ d))
  refine le_natCard_of_list [d, φ d, φ (φ d), φ (φ (φ d))] ?_ ?_
  · simp [Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm m1, Ne.symm m2, Ne.symm m3]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact SameCycle.refl _ _
    · exact sameCycle_apply_right.2 (SameCycle.refl _ _)
    · exact sameCycle_apply_right.2 (sameCycle_apply_right.2 (SameCycle.refl _ _))
    · exact sameCycle_apply_right.2 (sameCycle_apply_right.2
        (sameCycle_apply_right.2 (SameCycle.refl _ _)))

end Faces

/-- **Euler bound.** A finite plane graph with at least one edge and no single-edge component
has `|darts| + 12 ≤ 6 n'` (that is, `e ≤ 3 n' - 6`), `n'` the number of non-isolated
vertices. -/
theorem card_dart_add_twelve_le [Finite V] (hP : IsPlanar G) (hne : Nonempty G.Dart)
    (hedge : ∀ d : G.Dart, 2 ≤ Nat.card {u // G.Adj d.fst u} ∨
      2 ≤ Nat.card {u // G.Adj d.snd u}) :
    Nat.card G.Dart + 12 ≤ 6 * Nat.card {v // ∃ u, G.Adj v u} := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨P⟩ := hP
  have h0 := P.eulerDefect_eq_zero
  have hα := card_dart_eq_two_mul G
  have hφ : 3 * cycleCount (P.rot * dartSymm _) ≤ Nat.card G.Dart :=
    mul_numClasses_le _ 3 fun d => three_le_card_face_of_edge P.isRotationSystem hedge d
  have hK := one_le_numComponents P.rot (dartSymm G)
  have hn := cycleCount_eq_card_nonisolated P.isRotationSystem
  unfold eulerDefect at h0
  omega

/-- **Euler bound, triangle-free.** A finite triangle-free plane graph with at least one edge
and no single-edge component has `|darts| + 8 ≤ 4 n'` (that is, `e ≤ 2 n' - 4`). -/
theorem card_dart_add_eight_le_of_cliqueFree [Finite V] (hP : IsPlanar G)
    (hG : G.CliqueFree 3) (hne : Nonempty G.Dart)
    (hedge : ∀ d : G.Dart, 2 ≤ Nat.card {u // G.Adj d.fst u} ∨
      2 ≤ Nat.card {u // G.Adj d.snd u}) :
    Nat.card G.Dart + 8 ≤ 4 * Nat.card {v // ∃ u, G.Adj v u} := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨P⟩ := hP
  have h0 := P.eulerDefect_eq_zero
  have hα := card_dart_eq_two_mul G
  have hφ : 4 * cycleCount (P.rot * dartSymm _) ≤ Nat.card G.Dart :=
    mul_numClasses_le _ 4 fun d =>
      four_le_card_face_of_cliqueFree P.isRotationSystem hG hedge d
  have hK := one_le_numComponents P.rot (dartSymm G)
  have hn := cycleCount_eq_card_nonisolated P.isRotationSystem
  unfold eulerDefect at h0
  omega

end LeanPool.K5MinorFreeChoosability
