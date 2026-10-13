/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Grotzsch.GACases

/-!
# Grünbaum–Aksenov: Case 3

Let `G` be a smallest counterexample and `F = v₀ v₁ v₂ v₃` a four-face (Case 1). By Case 2 it has
no chord, and by Lemma 10 (`GAMin.lemma10`), after rotating `F`, there are a triangle `v₀ v₁ z`
and paths `z y v₂`, `z x v₃` with `z v₂`, `z v₃`, `y v₀`, `x v₁` not edges.
* **Case 3.1** (`GAMin.case31`): `x = y` (a 3-prism with a 4-face).
* **Case 3.2** (`GAMin.case32`): `x ≠ y`.
-/

@[expose] public section

noncomputable section

open Classical Finset Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

namespace Grotzsch

variable {V : Type} [Fintype V] {G : SimpleGraph V}

/-! ### Four-faces from faces of length four -/

/-- A face with exactly four darts in a plane map of minimum degree `≥ 2` is a `FourFace`. -/
theorem exists_fourFace_of_card (M : PlaneMap G) (hdeg : ∀ v, 2 ≤ Nat.card {u // G.Adj v u})
    (d : G.Dart) (h4 : Nat.card {e // SameCycle M.facePerm d e} = 4) :
    ∃ d₁ d₂ d₃, FourFace M d d₁ d₂ d₃ := by
  have hσ := M.isRotationSystem
  have ne1 : ∀ e, M.facePerm e ≠ e := fun e => face_ne_self hσ e
  have ne2 : ∀ e, M.facePerm (M.facePerm e) ≠ e := fun e => face_face_ne_self hσ hdeg e
  have nosymm : ∀ e : G.Dart, M.facePerm e ≠ e.symm := by
    intro e he
    rw [PlaneMap.facePerm_apply] at he
    have h1 := card_neighbor_le_card_sameCycle hσ e.symm
    have h2 : Nat.card {e' // SameCycle M.rot e.symm e'} ≤ 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_le_one_iff_subsingleton]
      refine ⟨fun a b => Subtype.ext ?_⟩
      exact (a.2.eq_of_left he).symm.trans (b.2.eq_of_left he)
    have := hdeg e.symm.fst
    omega
  set f := M.facePerm with hf
  set O := Finset.univ.filter fun e => SameCycle f d e with hO
  have hOc : O.card = 4 := by rw [← h4, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have mem : ∀ n : ℕ, (f ^ n) d ∈ O := fun n => by
    simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨n, by simp⟩
  have m1 : f d ∈ O := by simpa using mem 1
  have m2 : f (f d) ∈ O := by simpa [pow_succ] using mem 2
  have m3 : f (f (f d)) ∈ O := by simpa [pow_succ] using mem 3
  have m4 : f (f (f (f d))) ∈ O := by simpa [pow_succ] using mem 4
  have m0 : d ∈ O := by simpa using mem 0
  -- `f³ d ≠ d`, otherwise the face has at most three darts
  have ne3 : f (f (f d)) ≠ d := by
    intro h3
    have hsub : O ⊆ {d, f d, f (f d)} := by
      intro e he
      simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and] at he
      obtain ⟨n, hn⟩ := he.exists_nat_pow_eq
      subst hn
      clear he
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', Perm.mul_apply]
        simp only [Finset.mem_insert, Finset.mem_singleton] at ih ⊢
        rcases ih with h | h | h <;> rw [h]
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl h3
    have := Finset.card_le_card hsub
    have := Finset.card_le_three (a := d) (b := f d) (c := f (f d))
    omega
  have hS : ({d, f d, f (f d), f (f (f d))} : Finset G.Dart).card = 4 := by
    have a1 : f (f (f d)) ≠ f d := fun h => ne2 d (f.injective h)
    rw [Finset.card_insert_of_notMem (by simp [(ne1 d).symm, (ne2 d).symm, ne3.symm]),
      Finset.card_insert_of_notMem (by simp [(ne1 _).symm, a1.symm]),
      Finset.card_insert_of_notMem (by simp [(ne1 _).symm]), Finset.card_singleton]
  have hSO : ({d, f d, f (f d), f (f (f d))} : Finset G.Dart) ⊆ O := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;> assumption
  have hEq := Finset.eq_of_subset_of_card_le hSO (by omega)
  have h4' : f (f (f (f d))) = d := by
    rw [← hEq] at m4
    simp only [Finset.mem_insert, Finset.mem_singleton] at m4
    rcases m4 with h | h | h | h
    · exact h
    · exact absurd (f.injective h) ne3
    · exact absurd (f.injective (f.injective h)) (ne2 _)
    · exact absurd h (ne1 _)
  refine ⟨f d, f (f d), f (f (f d)), rfl, rfl, rfl, h4', fun e he => ?_, ?_, ?_⟩
  · have : e ∈ O := by
      simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and]
      exact he
    rw [← hEq] at this
    simpa using this
  · intro h
    have e1 := facePerm_fst' M d
    have e2 := facePerm_fst' M (M.facePerm d)
    exact nosymm d (dart_eq_of (by rw [e1]; rfl) (by rw [dart_symm_snd, h, e2]))
  · intro h
    have e2 := facePerm_fst' M (M.facePerm d)
    have e3 := facePerm_fst' M (M.facePerm (M.facePerm d))
    exact nosymm (f d) (dart_eq_of (by rw [e2]; rfl) (by rw [dart_symm_snd, h, e3]))

/-- A smallest counterexample has a `FourFace`. -/
theorem GAMin.exists_fourFace (hG : GAMin G) (M : PlaneMap G) :
    ∃ d₀ d₁ d₂ d₃, FourFace M d₀ d₁ d₂ d₃ := by
  obtain ⟨d, hd⟩ := hG.exists_four_face M
  have hdeg : ∀ v, 2 ≤ Nat.card {u // G.Adj v u} := fun v => by
    rw [card_adj_eq_degree]; have := hG.isCritical4.three_le_degree v; omega
  obtain ⟨d₁, d₂, d₃, h⟩ := exists_fourFace_of_card M hdeg d hd
  exact ⟨d, d₁, d₂, d₃, h⟩

/-! ### Lemma 10 -/

/-- **BKLY Lemma 10.** For a four-face of a smallest counterexample, after rotating it to
`v₀ v₁ v₂ v₃`, there are a triangle `v₀ v₁ z` and paths `z y v₂`, `z x v₃` with `z v₂`, `z v₃`,
`y v₀` and `x v₁` not edges. -/
theorem GAMin.lemma10 (hG : GAMin G) (M : PlaneMap G) {d₀ d₁ d₂ d₃ : G.Dart}
    (hF : FourFace M d₀ d₁ d₂ d₃) :
    ∃ e₀ e₁ e₂ e₃ : G.Dart, FourFace M e₀ e₁ e₂ e₃ ∧ ∃ z y x : V,
      G.Adj e₀.fst z ∧ G.Adj e₁.fst z ∧ G.Adj z y ∧ G.Adj y e₂.fst ∧ G.Adj z x ∧
      G.Adj x e₃.fst ∧ ¬ G.Adj z e₂.fst ∧ ¬ G.Adj z e₃.fst ∧ ¬ G.Adj y e₀.fst ∧
      ¬ G.Adj x e₁.fst := by
  obtain ⟨p, q, hp0, hpq, hq2, np2, nq0⟩ := hG.exists_path_of_fourFace M hF
  obtain ⟨p', q', hp1, hpq', hq3, np3, nq1⟩ := hG.exists_path_of_fourFace M hF.rotate
  have h02 := hG.not_adj_of_fourFace M hF
  have h13 := hG.not_adj_of_fourFace M hF.rotate
  have a01 := hF.adj₀
  have a12 := hF.adj₁
  have a23 := hF.adj₂
  have a30 := hF.adj₃
  by_cases c1 : p = p'
  · subst c1
    exact ⟨d₀, d₁, d₂, d₃, hF, p, q, q', hp0, hp1, hpq, hq2, hpq', hq3, np2, np3, nq0, nq1⟩
  by_cases c2 : q = q'
  · subst c2
    exact ⟨d₂, d₃, d₀, d₁, hF.rotate.rotate, q, p, p', hq2.symm, hq3.symm, hpq.symm, hp0.symm,
      hpq'.symm, hp1.symm, nq0, nq1, np2, np3⟩
  by_cases c3 : p = q'
  · subst c3
    exact ⟨d₃, d₀, d₁, d₂, hF.rotate.rotate.rotate, p, p', q, hq3.symm, hp0, hpq'.symm,
      hp1.symm, hpq, hq2, nq1, np2, np3, nq0⟩
  by_cases c4 : q = p'
  · subst c4
    exact ⟨d₁, d₂, d₃, d₀, hF.rotate, q, q', p, hp1, hq2.symm, hpq', hq3, hpq.symm, hp0.symm,
      np3, nq0, nq1, np2⟩
  exfalso
  refine no_crossing_paths_of_ne M d₀ hF.inj a01 a12 a23 a30 hF.ne02 hF.ne13
    hF.mem_faceVerts.1 hF.mem_faceVerts.2.1 hF.mem_faceVerts.2.2.1 hF.mem_faceVerts.2.2.2
    hp0 hpq hq2 hp1 hpq' hq3 ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩
    c1 c3 c4 c2
  · exact hp0.ne.symm
  · rintro rfl; exact np2 a12
  · rintro rfl; exact h02 hp0
  · rintro rfl; exact np2 a23.symm
  · rintro rfl; exact h02 hq2
  · rintro rfl; exact nq0 a01.symm
  · exact hq2.ne
  · rintro rfl; exact nq0 a30
  · rintro rfl; exact np3 a30.symm
  · exact hp1.ne.symm
  · rintro rfl; exact np3 a23
  · rintro rfl; exact h13 hp1
  · rintro rfl; exact nq1 a01
  · rintro rfl; exact h13 hq3
  · rintro rfl; exact nq1 a12.symm
  · exact hq3.ne

/-! ### Cases 3.1 and 3.2 -/

/-- **Case 3.1** (`x = y`): a 3-prism `v₀ v₁ z`, `v₂ v₃ x` whose 4-cycle `v₀ v₁ v₂ v₃` is a face.
-/
theorem GAMin.case31 (hG : GAMin G) (M : PlaneMap G) {e₀ e₁ e₂ e₃ : G.Dart}
    (hF : FourFace M e₀ e₁ e₂ e₃) {z x : V} (h0 : G.Adj e₀.fst z) (h1 : G.Adj e₁.fst z)
    (hzx : G.Adj z x) (hx2 : G.Adj x e₂.fst) (hx3 : G.Adj x e₃.fst) (n2 : ¬ G.Adj z e₂.fst)
    (n3 : ¬ G.Adj z e₃.fst) (nx0 : ¬ G.Adj x e₀.fst) (nx1 : ¬ G.Adj x e₁.fst) : False := by
  sorry

/-- **Case 3.2** (`x ≠ y`). -/
theorem GAMin.case32 (hG : GAMin G) (M : PlaneMap G) {e₀ e₁ e₂ e₃ : G.Dart}
    (hF : FourFace M e₀ e₁ e₂ e₃) {z y x : V} (h0 : G.Adj e₀.fst z) (h1 : G.Adj e₁.fst z)
    (hzy : G.Adj z y) (hy2 : G.Adj y e₂.fst) (hzx : G.Adj z x) (hx3 : G.Adj x e₃.fst)
    (n2 : ¬ G.Adj z e₂.fst) (n3 : ¬ G.Adj z e₃.fst) (ny0 : ¬ G.Adj y e₀.fst)
    (nx1 : ¬ G.Adj x e₁.fst) (hxy : x ≠ y) : False := by
  sorry

/-- **Case 3.** There is no smallest counterexample. -/
theorem GAMin.case3 (hG : GAMin G) : False := by
  obtain ⟨M⟩ := hG.planar
  obtain ⟨d₀, d₁, d₂, d₃, hF⟩ := hG.exists_fourFace M
  obtain ⟨e₀, e₁, e₂, e₃, hE, z, y, x, h0, h1, hzy, hy2, hzx, hx3, n2, n3, ny0, nx1⟩ :=
    hG.lemma10 M hF
  by_cases hxy : x = y
  · subst hxy
    exact hG.case31 M hE h0 h1 hzx hy2 hx3 n2 n3 ny0 nx1
  · exact hG.case32 M hE h0 h1 hzy hy2 hzx hx3 n2 n3 ny0 nx1 hxy

end Grotzsch
