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

/-! ### Case 3.1: auxiliary results -/

omit [Fintype V] in
theorem c31_ne_of_mem {s t : Finset V} {u : V} (hs : u ∈ s) (ht : u ∉ t) : s ≠ t :=
  fun h => ht (h ▸ hs)

theorem c31_four_le_triCount {s₁ s₂ s₃ s₄ : Finset V} (h₁ : G.IsNClique 3 s₁)
    (h₂ : G.IsNClique 3 s₂) (h₃ : G.IsNClique 3 s₃) (h₄ : G.IsNClique 3 s₄) (h12 : s₁ ≠ s₂)
    (h13 : s₁ ≠ s₃) (h14 : s₁ ≠ s₄) (h23 : s₂ ≠ s₃) (h24 : s₂ ≠ s₄) (h34 : s₃ ≠ s₄) :
    4 ≤ triCount G := by
  have hc : ({s₁, s₂, s₃, s₄} : Finset (Finset V)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_insert_of_notMem (by simp [h23, h24]),
      Finset.card_insert_of_notMem (by simp [h34]), Finset.card_singleton]
  have hsub : ({s₁, s₂, s₃, s₄} : Finset (Finset V)) ⊆
      Finset.univ.filter (fun s => G.IsNClique 3 s) := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hs with rfl | rfl | rfl | rfl <;> assumption
  unfold triCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact hc ▸ Finset.card_le_card hsub

omit [Fintype V] in
/-- At every vertex of a face cycle, the rotation takes one cycle neighbour to the other. -/
theorem c31_facial_rot (M : PlaneMap G) {k : ℕ} [NeZero k] {c : ZMod k → V}
    (h : IsCycFace M.rot c ∨ IsCycFace M.rot (fun i => c (-i))) (i : ZMod k)
    (d e : G.Dart) (hd1 : d.fst = c i) (hd2 : d.snd = c (i - 1)) (he1 : e.fst = c i)
    (he2 : e.snd = c (i + 1)) : M.rot d = e ∨ M.rot e = d := by
  rcases h with h | h
  · exact Or.inl (h i d e hd1 hd2 he1 he2)
  · right
    refine h (-i) e d (by simpa using he1) ?_ (by simpa using hd1) ?_
    · rw [he2]; congr 1; ring
    · rw [hd2]; congr 1; ring

omit [Fintype V] in
/-- Three darts at a vertex closed under the rotation contain all darts at that vertex. -/
theorem c31_nbr_of_rot (M : PlaneMap G) {w p₁ p₂ p₃ : V} (h13 : p₁ ≠ p₃)
    (h23 : p₂ ≠ p₃) (d₁ d₂ d₃ : G.Dart) (f1 : d₁.fst = w) (f2 : d₂.fst = w) (f3 : d₃.fst = w)
    (s1 : d₁.snd = p₁) (s2 : d₂.snd = p₂) (s3 : d₃.snd = p₃) (hF : M.rot d₁ = d₂)
    (hX : M.rot d₂ = d₃ ∨ M.rot d₃ = d₂) (hY : M.rot d₃ = d₁ ∨ M.rot d₁ = d₃) :
    ∀ u, G.Adj w u → u = p₁ ∨ u = p₂ ∨ u = p₃ := by
  have r23 : M.rot d₂ = d₃ := by
    rcases hX with h | h
    · exact h
    · have := M.rot.injective (h.trans hF.symm)
      exact absurd (s1 ▸ s3 ▸ congrArg (fun d : G.Dart => d.snd) this) h13.symm
  have r31 : M.rot d₃ = d₁ := by
    rcases hY with h | h
    · exact h
    · have := hF.symm.trans h
      exact absurd (s2 ▸ s3 ▸ congrArg (fun d : G.Dart => d.snd) this) h23
  have i1 : M.rot⁻¹ d₁ = d₃ := by rw [Perm.inv_eq_iff_eq]; exact r31.symm
  have i2 : M.rot⁻¹ d₂ = d₁ := by rw [Perm.inv_eq_iff_eq]; exact hF.symm
  have i3 : M.rot⁻¹ d₃ = d₂ := by rw [Perm.inv_eq_iff_eq]; exact r23.symm
  have hmem : ∀ i : ℤ, (M.rot ^ i) d₁ = d₁ ∨ (M.rot ^ i) d₁ = d₂ ∨ (M.rot ^ i) d₁ = d₃ := by
    intro i
    induction i using Int.induction_on with
    | zero => simp
    | succ i ih =>
      rw [add_comm, zpow_add, zpow_one, Perm.mul_apply]
      rcases ih with h | h | h <;> rw [h]
      · exact Or.inr (Or.inl hF)
      · exact Or.inr (Or.inr r23)
      · exact Or.inl r31
    | pred i ih =>
      rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one, Perm.mul_apply]
      rcases ih with h | h | h <;> rw [h]
      · exact Or.inr (Or.inr i1)
      · exact Or.inl i2
      · exact Or.inr (Or.inl i3)
  intro u hu
  obtain ⟨i, hi⟩ := M.isRotationSystem.sameCycle d₁ ⟨(w, u), hu⟩ f1
  rcases hmem i with h | h | h <;> rw [h] at hi <;> subst hi
  · exact Or.inl s1
  · exact Or.inr (Or.inl s2)
  · exact Or.inr (Or.inr s3)

/-- A triangle is a face: at each corner the rotation takes one side to the other. -/
theorem c31_tri_rot (hG : GAMin G) (M : PlaneMap G) {a b c : V} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hac : G.Adj a c) (d e : G.Dart) (hd1 : d.fst = a) (hd2 : d.snd = c)
    (he1 : e.fst = a) (he2 : e.snd = b) : M.rot d = e ∨ M.rot e = d := by
  have n1 := hab.ne
  have n2 := hbc.ne
  have n3 := hac.ne
  let cc : ZMod 3 → V := fun i => (![a, b, c] : Fin 3 → V) i
  have hcyc : IsCycleMap G cc := by
    refine ⟨fun i j h => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp [cc] at h; simp_all)
    · fin_cases i
      · exact hab
      · exact hbc
      · exact hac.symm
  have hch : IsChordless G cc := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | (left; rfl) | (right; rfl) | exact (h.ne rfl).elim
  have hS : ∀ u ∈ Set.range cc, ∀ v ∈ Set.range cc, u ≠ v → G.Adj u v := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    fin_cases i <;> fin_cases j <;> simp [cc] at hne ⊢ <;>
      first | exact hab | exact hbc | exact hac | exact hab.symm | exact hbc.symm | exact hac.symm
  exact c31_facial_rot M (cycle_facial M (by norm_num) hcyc hch
    (fun d e hd he => hG.rIn_of_clique hS hd he)) 0 d e hd1 hd2 he1 he2

omit [Fintype V] in
theorem c31_mem_range_four {a b c d u : V} :
    u ∈ Set.range (fun i : ZMod 4 => (![a, b, c, d] : Fin 4 → V) i) ↔
      u = a ∨ u = b ∨ u = c ∨ u = d := by
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

/-- A `K₅` minor in a planar apex extension. -/
theorem c31_k5 {S : Set V} (hP : IsPlanar (apexExtend G S)) {a₁ a₂ b₁ b₂ c d₁ d₂ : V}
    (ha : G.Adj a₁ a₂) (hb : G.Adj b₁ b₂) (hd : G.Adj d₁ d₂) (hab : G.Adj a₁ b₁)
    (hac : G.Adj a₂ c) (had : G.Adj a₁ d₁) (hbc : G.Adj b₁ c) (hbd : G.Adj b₂ d₂)
    (hcd : G.Adj c d₁) (sa : a₁ ∈ S) (sb : b₁ ∈ S) (sc : c ∈ S) (sd : d₁ ∈ S)
    (e1 : a₁ ≠ b₂) (e2 : a₂ ≠ b₁) (e3 : a₂ ≠ b₂) (e4 : a₁ ≠ c) (e5 : a₁ ≠ d₂) (e6 : a₂ ≠ d₁)
    (e7 : a₂ ≠ d₂) (e8 : b₂ ≠ c) (e9 : b₁ ≠ d₁) (e10 : b₁ ≠ d₂) (e11 : b₂ ≠ d₁)
    (e13 : c ≠ d₂) : False := by
  have e14 := hab.ne; have e15 := hac.ne; have e16 := had.ne; have e17 := hbc.ne
  have e18 := hbd.ne; have e19 := hcd.ne; have e20 := ha.ne; have e21 := hb.ne
  have e22 := hd.ne
  set A := apexExtend G S
  have conn2 : ∀ p q : V, G.Adj p q →
      (A.induce (↑({some p, some q} : Finset (Option V)) : Set (Option V))).Connected := by
    intro p q hpq
    rw [← connSet_iff_induce_connected]
    have := (connSet_singleton A (some q)).insert_adj (a := some p) (Set.mem_singleton _) hpq
    simpa using this
  let br : Fin 5 → Finset (Option V) :=
    ![{none}, {some a₁, some a₂}, {some b₁, some b₂}, {some c}, {some d₁, some d₂}]
  refine cliqueMinorFree_five_of_isPlanar hP ⟨{
    branch := br
    branch_nonempty := fun i => by fin_cases i <;> simp [br]
    branch_connected := fun i => ?_
    branch_disjoint := fun i j hij => ?_
    branch_adjacent := fun i j hij => ?_ }⟩
  · fin_cases i
    · rw [← connSet_iff_induce_connected]; simpa [br] using connSet_singleton A none
    · exact conn2 a₁ a₂ ha
    · exact conn2 b₁ b₂ hb
    · rw [← connSet_iff_induce_connected]; simpa [br] using connSet_singleton A (some c)
    · exact conn2 d₁ d₂ hd
  · rw [Finset.disjoint_left]
    fin_cases i <;> fin_cases j <;> simp_all [br, eq_comm]
  · have key : ∀ i j : Fin 5, i < j → ∃ p ∈ br i, ∃ q ∈ br j, A.Adj p q := by
      intro i j hlt
      fin_cases i <;> fin_cases j <;> first | (exfalso; revert hlt; decide) | skip
      · exact ⟨none, by simp [br], some a₁, by simp [br], sa⟩
      · exact ⟨none, by simp [br], some b₁, by simp [br], sb⟩
      · exact ⟨none, by simp [br], some c, by simp [br], sc⟩
      · exact ⟨none, by simp [br], some d₁, by simp [br], sd⟩
      · exact ⟨some a₁, by simp [br], some b₁, by simp [br], hab⟩
      · exact ⟨some a₂, by simp [br], some c, by simp [br], hac⟩
      · exact ⟨some a₁, by simp [br], some d₁, by simp [br], had⟩
      · exact ⟨some b₁, by simp [br], some c, by simp [br], hbc⟩
      · exact ⟨some b₂, by simp [br], some d₂, by simp [br], hbd⟩
      · exact ⟨some c, by simp [br], some d₁, by simp [br], hcd⟩
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · obtain ⟨p, hp, q, hq, hpq⟩ := key j i h
      exact ⟨q, hq, p, hp, hpq.symm⟩

/-- One side of a separating set with the extension property, away from a given edge. -/
theorem c31_side (hG : GAMin G) {S : Set V} (hext : ExtProp G S) {d e : G.Dart}
    (hd : d.fst ∉ S) (he : e.fst ∉ S) (hde : ¬ RIn G Sᶜ d.fst e.fst) {a b : V}
    (hab : G.Adj a b) (ha : a ∉ S) (hb : b ∉ S) :
    ∃ (B : Set V) (t : Finset V), (∀ u v, u ∈ B → u ∉ S → G.Adj u v → v ∈ B) ∧ a ∉ B ∧
      b ∉ B ∧ G.IsNClique 3 t ∧ ∀ u ∈ t, u ∈ B := by
  obtain ⟨A, B, hSA, hSB, hAB, hcross, hA, hB⟩ := hG.sides hext hd he hde
  have tri : ∀ X : Set V, ¬ (restrict G X).CliqueFree 3 →
      ∃ t : Finset V, G.IsNClique 3 t ∧ ∀ u ∈ t, u ∈ X := by
    intro X hX
    simp only [SimpleGraph.CliqueFree, not_forall, not_not] at hX
    obtain ⟨t, ht⟩ := hX
    refine ⟨t, ht.mono (restrict_le G X), fun u hu => ?_⟩
    obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := SimpleGraph.is3Clique_iff.mp ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact hpq.2.1
    · exact hpq.2.2
    · exact hpr.2.2
  rcases hcross a b hab with ⟨haA, hbA⟩ | ⟨haB, hbB⟩
  · obtain ⟨t, ht, htB⟩ := tri B hB
    refine ⟨B, t, fun u v hu huS huv => ?_, fun h => ha (hAB a haA h),
      fun h => hb (hAB b hbA h), ht, htB⟩
    rcases hcross u v huv with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd (hAB u h1 hu) huS
    · exact h2
  · obtain ⟨t, ht, htA⟩ := tri A hA
    refine ⟨A, t, fun u v hu huS huv => ?_, fun h => ha (hAB a h haB),
      fun h => hb (hAB b h hbB), ht, htA⟩
    rcases hcross u v huv with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd (hAB u hu h1) huS

/-! ### Triangles after identifying two vertices -/

omit [Fintype V] in
theorem c31_glue_adj_plain {x z : V} {p q : {v // v ≠ z}} (hp : p.1 ≠ x) (hq : q.1 ≠ x)
    (h : (glue G x z).Adj p q) : G.Adj p q := by
  rcases h.2 with h' | h' | h'
  · exact h'
  · exact absurd h'.1 hp
  · exact absurd h'.1 hq

omit [Fintype V] in
theorem c31_glue_adj_fromx {x z : V} {p q : {v // v ≠ z}} (hp : p.1 = x) (hq : q.1 ≠ x)
    (h : (glue G x z).Adj p q) : G.Adj x q ∨ G.Adj z q := by
  rcases h.2 with h' | h' | h'
  · exact Or.inl (hp ▸ h')
  · exact Or.inr h'.2
  · exact absurd h'.1 hq

omit [Fintype V] in
theorem c31_glue_main {p q r z x : V}
    (H : ∀ a b, G.Adj p a → G.Adj a b → G.Adj b q → ¬ G.Adj a q → ¬ G.Adj b p → a ≠ r →
      b ≠ r → a = z ∧ b = x)
    {a b c : {v // v ≠ q}} (ha : a.1 = p) (hb : b.1 ≠ p) (hc : c.1 ≠ p)
    (hab : (glue G p q).Adj a b) (hac : (glue G p q).Adj a c) (hbc : (glue G p q).Adj b c)
    (hn1 : ¬ G.IsNClique 3 ({p, b.1, c.1} : Finset V))
    (hn2 : ¬ G.IsNClique 3 ({q, b.1, c.1} : Finset V)) (hbr : b.1 ≠ r) (hcr : c.1 ≠ r) :
    ({p, b.1, c.1} : Finset V) = {p, z, x} := by
  have hbc' := c31_glue_adj_plain hb hc hbc
  rcases c31_glue_adj_fromx ha hb hab with h1 | h1 <;>
    rcases c31_glue_adj_fromx ha hc hac with h2 | h2
  · exact (hn1 (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1, h2, hbc'⟩)).elim
  · obtain ⟨rfl, rfl⟩ := H b c h1 hbc' h2.symm
      (fun h => hn2 (SimpleGraph.is3Clique_triple_iff.mpr ⟨h.symm, h2, hbc'⟩))
      (fun h => hn1 (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1, h.symm, hbc'⟩)) hbr hcr
    rfl
  · obtain ⟨rfl, rfl⟩ := H c b h2 hbc'.symm h1.symm
      (fun h => hn2 (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1, h.symm, hbc'⟩))
      (fun h => hn1 (SimpleGraph.is3Clique_triple_iff.mpr ⟨h.symm, h2, hbc'⟩)) hcr hbr
    exact congrArg (insert p) (Finset.pair_comm _ _)
  · exact (hn2 (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1, h2, hbc'⟩)).elim

omit [Fintype V] in
theorem c31_glue_new {p q r z x : V}
    (H : ∀ a b, G.Adj p a → G.Adj a b → G.Adj b q → ¬ G.Adj a q → ¬ G.Adj b p → a ≠ r →
      b ≠ r → a = z ∧ b = x)
    {t : Finset {v // v ≠ q}} (ht : (glue G p q).IsNClique 3 t)
    (hr : r ∉ t.map (Function.Embedding.subtype _))
    (hn1 : ¬ G.IsNClique 3 (t.map (Function.Embedding.subtype _)))
    (hn2 : ¬ G.IsNClique 3 (insert q ((t.map (Function.Embedding.subtype _)).erase p))) :
    t.map (Function.Embedding.subtype _) = {p, z, x} := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := SimpleGraph.is3Clique_iff.mp ht
  have hmap : ({a, b, c} : Finset {v // v ≠ q}).map (Function.Embedding.subtype _) =
      {a.1, b.1, c.1} := by simp
  rw [hmap] at hr hn1 hn2 ⊢
  have hab' : a.1 ≠ b.1 := fun h => hab.1 (Subtype.ext h)
  have hac' : a.1 ≠ c.1 := fun h => hac.1 (Subtype.ext h)
  have hbc' : b.1 ≠ c.1 := fun h => hbc.1 (Subtype.ext h)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
  obtain ⟨har, hbr, hcr⟩ := hr
  by_cases ha : a.1 = p
  · subst ha
    rw [Finset.erase_insert (by simp [hab', hac'])] at hn2
    exact c31_glue_main H rfl (Ne.symm hab') (Ne.symm hac') hab hac hbc hn1 hn2
      (Ne.symm hbr) (Ne.symm hcr)
  by_cases hb : b.1 = p
  · subst hb
    have e : ({a.1, b.1, c.1} : Finset V) = {b.1, a.1, c.1} := Finset.insert_comm _ _ _
    rw [e] at hn1 hn2 ⊢
    rw [Finset.erase_insert (by simp [Ne.symm hab', hbc'])] at hn2
    exact c31_glue_main H rfl ha (Ne.symm hbc') hab.symm hbc hac hn1 hn2
      (Ne.symm har) (Ne.symm hcr)
  by_cases hc : c.1 = p
  · subst hc
    have e : ({a.1, b.1, c.1} : Finset V) = {c.1, a.1, b.1} := by
      ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [e] at hn1 hn2 ⊢
    rw [Finset.erase_insert (by simp [Ne.symm hac', Ne.symm hbc'])] at hn2
    exact c31_glue_main H rfl ha hb hac.symm hbc.symm hab hn1 hn2
      (Ne.symm har) (Ne.symm hbr)
  exact (hn1 (SimpleGraph.is3Clique_triple_iff.mpr ⟨c31_glue_adj_plain ha hb hab,
    c31_glue_adj_plain ha hc hac, c31_glue_adj_plain hb hc hbc⟩)).elim

omit [Fintype V] in
theorem c31_glue_tri_plain {x z : V} {t : Finset {v // v ≠ z}}
    (ht : (glue G x z).IsNClique 3 t) (hx : x ∉ t.map (Function.Embedding.subtype _)) :
    G.IsNClique 3 (t.map (Function.Embedding.subtype _)) := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := SimpleGraph.is3Clique_iff.mp ht
  have hmap : ({a, b, c} : Finset {v // v ≠ z}).map (Function.Embedding.subtype _) =
      {a.1, b.1, c.1} := by simp
  rw [hmap] at hx ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  obtain ⟨ha, hb, hc⟩ := hx
  exact SimpleGraph.is3Clique_triple_iff.mpr ⟨c31_glue_adj_plain (Ne.symm ha) (Ne.symm hb) hab,
    c31_glue_adj_plain (Ne.symm ha) (Ne.symm hc) hac,
    c31_glue_adj_plain (Ne.symm hb) (Ne.symm hc) hbc⟩

/-- If the only new triangle through the identified vertex (avoiding `r`) comes from the path
`p z x q`, the triangles avoiding `r` after identifying `p` and `q` are at most as many as the
triangles of `G`, provided some triangle of `G` contains `r`. -/
theorem c31_card_glue_tri {p q r z x : V}
    (H : ∀ a b, G.Adj p a → G.Adj a b → G.Adj b q → ¬ G.Adj a q → ¬ G.Adj b p → a ≠ r →
      b ≠ r → a = z ∧ b = x)
    {T : Finset V} (hT : G.IsNClique 3 T) (hrT : r ∈ T) (hrq : r ≠ q) :
    Nat.card {t : Finset {v // v ≠ q} //
      (glue G p q).IsNClique 3 t ∧ (⟨r, hrq⟩ : {v // v ≠ q}) ∉ t} ≤ triCount G := by
  let emb : {v // v ≠ q} ↪ V := Function.Embedding.subtype _
  let Y := {u : Finset V // G.IsNClique 3 u ∧ r ∉ u}
  have hY : Nat.card Y + 1 ≤ triCount G := by
    unfold triCount
    simp only [Y]
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Fintype.card_subtype]
    have hsub : Finset.univ.filter (fun u : Finset V => G.IsNClique 3 u ∧ r ∉ u) ⊂
        Finset.univ.filter (fun u : Finset V => G.IsNClique 3 u) := by
      refine (Finset.ssubset_iff_of_subset fun u hu => ?_).2 ⟨T, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢; exact hu.1
      · simpa using hT
      · simp [hrT]
    have := Finset.card_lt_card hsub
    omega
  have hzt : ∀ t : Finset {v // v ≠ q}, q ∉ t.map emb := fun t h => by
    obtain ⟨w, -, hw⟩ := Finset.mem_map.mp h
    exact w.2 hw
  have hrt : ∀ t : Finset {v // v ≠ q}, (⟨r, hrq⟩ : {v // v ≠ q}) ∉ t → r ∉ t.map emb :=
    fun t ht h => by
      obtain ⟨w, hw, hw'⟩ := Finset.mem_map.mp h
      exact ht (by
        have : w = ⟨r, hrq⟩ := Subtype.ext hw'
        exact this ▸ hw)
  have hrt2 : ∀ t : Finset {v // v ≠ q}, r ∉ insert q ((t.map emb).erase p) ∨
      (⟨r, hrq⟩ : {v // v ≠ q}) ∈ t := fun t => by
    by_cases ht : (⟨r, hrq⟩ : {v // v ≠ q}) ∈ t
    · exact Or.inr ht
    · left
      simp only [Finset.mem_insert, hrq, false_or]
      exact fun h => hrt t ht (Finset.mem_of_mem_erase h)
  let g : {t : Finset {v // v ≠ q} //
      (glue G p q).IsNClique 3 t ∧ (⟨r, hrq⟩ : {v // v ≠ q}) ∉ t} → Option Y := fun t =>
    if h1 : G.IsNClique 3 (t.1.map emb) then some ⟨_, h1, hrt _ t.2.2⟩
    else if h2 : G.IsNClique 3 (insert q ((t.1.map emb).erase p)) then
      some ⟨_, h2, (hrt2 t.1).resolve_right t.2.2⟩
    else none
  have hg : Function.Injective g := by
    rintro ⟨t, ht, htr⟩ ⟨t', ht', htr'⟩ h
    apply Subtype.ext
    show t = t'
    apply Finset.map_injective emb
    have hp : ∀ s : Finset {v // v ≠ q}, (glue G p q).IsNClique 3 s →
        ¬ G.IsNClique 3 (s.map emb) → p ∈ s.map emb := fun s hs hn => by
      by_contra hx
      exact hn (c31_glue_tri_plain hs hx)
    have hz1 : q ∉ (t.map emb).erase p := fun hm => hzt t (Finset.mem_of_mem_erase hm)
    have hz2 : q ∉ (t'.map emb).erase p := fun hm => hzt t' (Finset.mem_of_mem_erase hm)
    by_cases h1 : G.IsNClique 3 (t.map emb) <;> by_cases h3 : G.IsNClique 3 (t'.map emb)
    · simp only [g, h1, h3, ↓reduceDIte, Option.some.injEq] at h
      replace h := congrArg Subtype.val h; dsimp only at h
      exact h
    · by_cases h4 : G.IsNClique 3 (insert q ((t'.map emb).erase p))
      · simp only [g, h1, h3, h4, ↓reduceDIte, Option.some.injEq] at h
        replace h := congrArg Subtype.val h; dsimp only at h
        exact absurd (h ▸ Finset.mem_insert_self _ _) (hzt t)
      · simp [g, h1, h3, h4] at h
    · by_cases h2 : G.IsNClique 3 (insert q ((t.map emb).erase p))
      · simp only [g, h1, h3, h2, ↓reduceDIte, Option.some.injEq] at h
        replace h := congrArg Subtype.val h; dsimp only at h
        exact absurd (h.symm ▸ Finset.mem_insert_self _ _) (hzt t')
      · simp [g, h1, h3, h2] at h
    · by_cases h2 : G.IsNClique 3 (insert q ((t.map emb).erase p)) <;>
        by_cases h4 : G.IsNClique 3 (insert q ((t'.map emb).erase p))
      · simp only [g, h1, h3, h2, h4, ↓reduceDIte, Option.some.injEq] at h
        replace h := congrArg Subtype.val h; dsimp only at h
        have e' : (t.map emb).erase p = (t'.map emb).erase p := by
          rw [← Finset.erase_insert hz1, h, Finset.erase_insert hz2]
        rw [← Finset.insert_erase (hp t ht h1), ← Finset.insert_erase (hp t' ht' h3), e']
      · simp [g, h1, h3, h2, h4] at h
      · simp [g, h1, h3, h2, h4] at h
      · exact (c31_glue_new H ht (hrt t htr) h1 h2).trans
          (c31_glue_new H ht' (hrt t' htr') h3 h4).symm
  calc _ ≤ Nat.card (Option Y) := Nat.card_le_card_of_injective g hg
    _ = Nat.card Y + 1 := Finite.card_option
    _ ≤ triCount G := hY

theorem c31_card_edgeSet_le {W W' : Type} [Fintype W'] {X : SimpleGraph W}
    {Y : SimpleGraph W'} (f : W → W') (hf : Function.Injective f)
    (hadj : ∀ a b, X.Adj a b → Y.Adj (f a) (f b)) :
    Nat.card X.edgeSet ≤ Nat.card Y.edgeSet := by
  refine Nat.card_le_card_of_injective
    (fun e => ⟨Sym2.map f e.1, ?_⟩) fun e₁ e₂ h => ?_
  · obtain ⟨e, he⟩ := e
    induction e using Sym2.ind with
    | _ a b => exact hadj a b he
  · exact Subtype.ext (Sym2.map.injective hf (congrArg Subtype.val h))

/-- **Identifying the opposite corners `p`, `q` of a four-face.** If a neighbour `r` of `p` and
`q` has only one further neighbour `s` and lies on a triangle, then besides any given path
`p z x q` there is another path `p a b q` with `a q`, `b p` not edges, avoiding `r`. -/
theorem c31_glue_path (hG : GAMin G) (M : PlaneMap G) (o : G.Dart)
    (hinj : ∀ e e' : FaceApex.F M o, e.1.fst = e'.1.fst → e = e') {p q r s z x : V}
    (hp : p ∈ FaceApex.faceVerts M o) (hq : q ∈ FaceApex.faceVerts M o) (hpq : p ≠ q)
    (npq : ¬ G.Adj p q) (hrp : r ≠ p) (hrq : r ≠ q)
    (hN : ∀ u, G.Adj r u → u = p ∨ u = q ∨ u = s) {T : Finset V} (hT : G.IsNClique 3 T)
    (hrT : r ∈ T) :
    ∃ a b, G.Adj p a ∧ G.Adj a b ∧ G.Adj b q ∧ ¬ G.Adj a q ∧ ¬ G.Adj b p ∧ a ≠ r ∧
      b ≠ r ∧ ¬ (a = z ∧ b = x) := by
  by_contra hcon
  have H : ∀ a b, G.Adj p a → G.Adj a b → G.Adj b q → ¬ G.Adj a q → ¬ G.Adj b p → a ≠ r →
      b ≠ r → a = z ∧ b = x := by
    intro a b h1 h2 h3 h4 h5 h6 h7
    by_contra h8
    exact hcon ⟨a, b, h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hnc : ¬ (glue G p q).Colorable 3 := fun h => hG.not_colorable (colorable_of_glue hpq npq h)
  obtain ⟨S, H', hsub, hcrit⟩ := exists_critical_subgraph (glue G p q) hnc
  have hrS : (⟨r, hrq⟩ : {v // v ≠ q}) ∉ S := by
    intro hrS
    have h3 := hcrit.three_le_degree ⟨⟨r, hrq⟩, hrS⟩
    have h2 : H'.degree ⟨⟨r, hrq⟩, hrS⟩ ≤ 2 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      calc _ ≤ ({p, s} : Finset V).card :=
            Finset.card_le_card_of_injOn (fun w => w.1.1) (fun w hw => ?_)
              (fun w _ w' _ h => Subtype.ext (Subtype.ext h))
        _ ≤ 2 := Finset.card_le_two
      have hw' := hsub _ _ ((SimpleGraph.mem_neighborFinset _ _ _).1 hw)
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      rcases hw'.2 with h | ⟨h, -⟩ | ⟨h, -⟩
      · rcases hN _ h with h' | h' | h'
        · exact Or.inl h'
        · exact absurd h' w.1.2
        · exact Or.inr h'
      · exact absurd h hrp
      · exact Or.inl h
    omega
  have htri : triCount H' ≤ triCount G := by
    refine le_trans ?_ (c31_card_glue_tri H hT hrT hrq)
    let emb : (↥S) ↪ {v // v ≠ q} := Function.Embedding.subtype _
    have hle : H'.map emb ≤ glue G p q := by
      intro u v h
      obtain ⟨a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj emb H' u v).1 h
      exact hsub a b hab
    refine Nat.card_le_card_of_injective (fun t => ⟨t.1.map emb, (t.2.map).mono hle, ?_⟩) ?_
    · intro hm
      obtain ⟨w, -, hw⟩ := Finset.mem_map.mp hm
      exact hrS (hw ▸ w.2)
    · intro t t' h
      exact Subtype.ext (Finset.map_injective emb (congrArg Subtype.val h))
  refine hcrit.not_colorable (hG.small (↥S) H' ?_ ?_ (htri.trans hG.tri))
  · have h1 : Fintype.card (↥S) ≤ Fintype.card {v // v ≠ q} := Fintype.card_le_of_injective
      Subtype.val Subtype.val_injective
    have h2 : Fintype.card {v // v ≠ q} < Fintype.card V :=
      Fintype.card_subtype_lt (p := (· ≠ q)) (x := q) (by simp)
    have h3 := c31_card_edgeSet_le (X := H') (Y := glue G p q) Subtype.val
      Subtype.val_injective hsub
    have h4 := card_edgeSet_glue_le (G := G) p q hpq
    omega
  · exact isPlanar_of_injective_hom' Subtype.val Subtype.val_injective hsub
      (isPlanar_glue M o hinj hpq hp hq)

/-- **Core of Case 3.1.** With the face `v₀ v₁ v₂ v₃`, the triangles `v₀ v₁ z`, `v₂ v₃ x`,
the neighbourhoods `N(v₁) = {v₀, v₂, z}`, `N(v₂) = {v₁, v₃, x}` and a planar apex extension
over `z, v₁, v₂, x`, there is no smallest counterexample. -/
theorem c31_core (hG : GAMin G) (M : PlaneMap G) (o : G.Dart)
    (hinj : ∀ e e' : FaceApex.F M o, e.1.fst = e'.1.fst → e = e') {v₀ v₁ v₂ v₃ z x : V}
    (m0 : v₀ ∈ FaceApex.faceVerts M o) (m1 : v₁ ∈ FaceApex.faceVerts M o)
    (m2 : v₂ ∈ FaceApex.faceVerts M o) (m3 : v₃ ∈ FaceApex.faceVerts M o)
    (a01 : G.Adj v₀ v₁) (a12 : G.Adj v₁ v₂) (a23 : G.Adj v₂ v₃) (a30 : G.Adj v₃ v₀)
    (ne02 : v₀ ≠ v₂) (ne13 : v₁ ≠ v₃) (n02 : ¬ G.Adj v₀ v₂) (n13 : ¬ G.Adj v₁ v₃)
    (h0 : G.Adj v₀ z) (h1 : G.Adj v₁ z) (hzx : G.Adj z x) (hx2 : G.Adj x v₂)
    (hx3 : G.Adj x v₃) (n2 : ¬ G.Adj z v₂) (n3 : ¬ G.Adj z v₃) (nx0 : ¬ G.Adj x v₀)
    (nx1 : ¬ G.Adj x v₁) {S : Set V} (hP : IsPlanar (apexExtend G S)) (sz : z ∈ S)
    (s1 : v₁ ∈ S) (s2 : v₂ ∈ S) (sx : x ∈ S)
    (hN1 : ∀ u, G.Adj v₁ u → u = v₀ ∨ u = v₂ ∨ u = z)
    (hN2 : ∀ u, G.Adj v₂ u → u = v₁ ∨ u = v₃ ∨ u = x) : False := by
  have z0 : z ≠ v₀ := h0.ne.symm
  have z1 : z ≠ v₁ := h1.ne.symm
  have z2 : z ≠ v₂ := fun h => n02 (h ▸ h0)
  have z3 : z ≠ v₃ := fun h => n13 (h ▸ h1)
  have x0 : x ≠ v₀ := fun h => n02 (h ▸ hx2)
  have x1 : x ≠ v₁ := fun h => n13 (h ▸ hx3)
  have x2 : x ≠ v₂ := hx2.ne
  have x3 : x ≠ v₃ := hx3.ne
  have zx : z ≠ x := hzx.ne
  have d01 := a01.ne; have d12 := a12.ne; have d23 := a23.ne; have d30 := a30.ne
  -- identifying `v₀` and `v₂`
  obtain ⟨a, b, pa, ab, bq, naq, nbp, ar, br, hab⟩ := c31_glue_path (z := z) (x := x) hG M o
    hinj m0 m2 ne02 n02 d01.symm d12 hN1
    (SimpleGraph.is3Clique_triple_iff.mpr ⟨a01, h0, h1⟩) (by simp)
  have a0 : a ≠ v₀ := pa.ne.symm
  have a2 : a ≠ v₂ := fun h => n02 (h ▸ pa)
  have a3 : a ≠ v₃ := fun h => naq (h ▸ a23.symm)
  have b0 : b ≠ v₀ := fun h => n02 (h ▸ bq)
  have b2 : b ≠ v₂ := bq.ne
  have b3 : b ≠ v₃ := fun h => nbp (h ▸ a30)
  have hbx : b = x ∧ a ≠ z := by
    by_cases e1 : a = z
    · subst e1
      have bx : b ≠ x := fun h => hab ⟨rfl, h⟩
      exact (c31_k5 hP ab a01.symm hx3 h1.symm bq hzx a12 a30.symm hx2.symm sz s1 s2 sx z0 br
        b0 z2 z3 bx b3 ne02 x1.symm ne13 x0.symm d23).elim
    by_cases e2 : a = x
    · exact (nx0 (e2 ▸ pa).symm).elim
    by_cases e3 : b = z
    · exact (n2 (e3 ▸ bq)).elim
    by_cases e4 : b = x
    · exact ⟨e4, e1⟩
    exact (no_crossing_paths_of_ne M o hinj a01 a12 a23 a30 ne02 ne13 m0 m1 m2 m3 pa ab bq h1
      hzx hx3 ⟨a0, ar, a2, a3⟩ ⟨b0, br, b2, b3⟩ ⟨z0, z1, z2, z3⟩ ⟨x0, x1, x2, x3⟩ e1 e2
      e3 e4).elim
  obtain ⟨hbx, az⟩ := hbx
  subst b
  -- identifying `v₁` and `v₃`
  obtain ⟨a', b', pa', ab', bq', naq', nbp', ar', br', hab'⟩ := c31_glue_path (z := z)
    (x := x) hG M o hinj m1 m3 ne13 n13 d12.symm d23 hN2
    (SimpleGraph.is3Clique_triple_iff.mpr ⟨a23, hx2.symm, hx3.symm⟩) (by simp)
  have a'1 : a' ≠ v₁ := pa'.ne.symm
  have a'3 : a' ≠ v₃ := fun h => n13 (h ▸ pa')
  have a'0 : a' ≠ v₀ := fun h => naq' (h ▸ a30.symm)
  have b'3 : b' ≠ v₃ := bq'.ne
  have b'1 : b' ≠ v₁ := fun h => n13 (h ▸ bq')
  have b'0 : b' ≠ v₀ := fun h => nbp' (h ▸ a01)
  have haz : a' = z ∧ b' ≠ x := by
    by_cases e4 : x = b'
    · subst b'
      have a'z : a' ≠ z := fun h => hab' ⟨h, rfl⟩
      exact (c31_k5 hP pa' h0.symm a23 h1 ab' a12 hzx a30.symm hx2 s1 sz sx s2 d01.symm a'z a'0
        x1.symm ne13 ar' a'3 x0.symm z2 z3 ne02 x3).elim
    by_cases e2 : z = b'
    · exact (n3 (e2 ▸ bq')).elim
    by_cases e3 : x = a'
    · exact (nx1 (e3 ▸ pa').symm).elim
    by_cases e1 : z = a'
    · exact ⟨e1.symm, Ne.symm e4⟩
    exact (no_crossing_paths_of_ne M o hinj a01 a12 a23 a30 ne02 ne13 m0 m1 m2 m3 h0 hzx hx2
      pa' ab' bq' ⟨z0, z1, z2, z3⟩ ⟨x0, x1, x2, x3⟩ ⟨a'0, a'1, ar', a'3⟩
      ⟨b'0, b'1, br', b'3⟩ e1 e2 e3 e4).elim
  obtain ⟨haz, b'x⟩ := haz
  subst a'
  by_cases hw : a = b'
  · subst b'
    have t1 : G.IsNClique 3 ({a, v₀, v₃} : Finset V) :=
      SimpleGraph.is3Clique_triple_iff.mpr ⟨pa.symm, bq', a30.symm⟩
    have t2 : G.IsNClique 3 ({a, z, x} : Finset V) :=
      SimpleGraph.is3Clique_triple_iff.mpr ⟨ab'.symm, ab, hzx⟩
    have t3 : G.IsNClique 3 ({v₀, v₁, z} : Finset V) :=
      SimpleGraph.is3Clique_triple_iff.mpr ⟨a01, h0, h1⟩
    have t4 : G.IsNClique 3 ({v₂, v₃, x} : Finset V) :=
      SimpleGraph.is3Clique_triple_iff.mpr ⟨a23, hx2.symm, hx3.symm⟩
    have := c31_four_le_triCount t1 t2 t3 t4
      (c31_ne_of_mem (u := v₀) (by simp) (by simp [a0.symm, z0.symm, x0.symm]))
      (c31_ne_of_mem (u := v₃) (by simp) (by simp [a30.ne, ne13.symm, z3.symm]))
      (c31_ne_of_mem (u := v₀) (by simp) (by simp [ne02, d30.symm, x0.symm]))
      (c31_ne_of_mem (u := x) (by simp) (by simp [x0, x1, zx.symm]))
      (c31_ne_of_mem (u := z) (by simp) (by simp [z2, z3, zx]))
      (c31_ne_of_mem (u := v₀) (by simp) (by simp [ne02, d30.symm, x0.symm]))
    have := hG.tri
    omega
  · exact no_crossing_paths_of_ne M o hinj a01 a12 a23 a30 ne02 ne13 m0 m1 m2 m3 pa ab hx2
      h1 ab' bq' ⟨a0, ar, a2, a3⟩ ⟨x0, x1, x2, x3⟩ ⟨z0, z1, z2, z3⟩ ⟨b'0, b'1, br', b'3⟩
      az hw zx.symm (Ne.symm b'x)

omit [Fintype V] in
theorem c31_cyc4 {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hda : G.Adj d a) (nac : ¬ G.Adj a c) (nbd : ¬ G.Adj b d) (eac : a ≠ c) (ebd : b ≠ d) :
    IsCycleMap G (fun i : ZMod 4 => (![a, b, c, d] : Fin 4 → V) i) ∧
      IsChordless G (fun i : ZMod 4 => (![a, b, c, d] : Fin 4 → V) i) := by
  have e1 := hab.ne; have e2 := hbc.ne; have e3 := hcd.ne; have e4 := hda.ne
  refine ⟨⟨fun i j h => ?_, fun i => ?_⟩, fun i j h => ?_⟩
  · fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp at h; simp_all)
  · fin_cases i
    · exact hab
    · exact hbc
    · exact hcd
    · exact hda
  · fin_cases i <;> fin_cases j <;>
      first
        | (left; rfl)
        | (right; rfl)
        | exact (h.ne rfl).elim
        | exact (nac h).elim
        | exact (nac h.symm).elim
        | exact (nbd h).elim
        | exact (nbd h.symm).elim

/-- **One of the two 4-cycles `z v₀ v₃ x`, `z v₁ v₂ x` does not separate.** Otherwise both
contain triangles on their far sides, which must be one and the same third triangle; a path from
it to `v₀` avoiding the edge `z x` has to cross one of the two cycles. -/
theorem c31_nonsep (hG : GAMin G) {v₀ v₁ v₂ v₃ z x : V}
    (a01 : G.Adj v₀ v₁) (a12 : G.Adj v₁ v₂) (a23 : G.Adj v₂ v₃) (a30 : G.Adj v₃ v₀)
    (ne02 : v₀ ≠ v₂) (ne13 : v₁ ≠ v₃) (n02 : ¬ G.Adj v₀ v₂) (n13 : ¬ G.Adj v₁ v₃)
    (h0 : G.Adj v₀ z) (h1 : G.Adj v₁ z) (hzx : G.Adj z x) (hx2 : G.Adj x v₂)
    (hx3 : G.Adj x v₃) (n2 : ¬ G.Adj z v₂) (n3 : ¬ G.Adj z v₃) (nx0 : ¬ G.Adj x v₀)
    (nx1 : ¬ G.Adj x v₁) :
    (∀ d e : G.Dart, d.fst ∉ Set.range (fun i : ZMod 4 => (![z, v₀, v₃, x] : Fin 4 → V) i) →
      e.fst ∉ Set.range (fun i : ZMod 4 => (![z, v₀, v₃, x] : Fin 4 → V) i) →
      RIn G (Set.range (fun i : ZMod 4 => (![z, v₀, v₃, x] : Fin 4 → V) i))ᶜ d.fst e.fst) ∨
    (∀ d e : G.Dart, d.fst ∉ Set.range (fun i : ZMod 4 => (![z, v₁, v₂, x] : Fin 4 → V) i) →
      e.fst ∉ Set.range (fun i : ZMod 4 => (![z, v₁, v₂, x] : Fin 4 → V) i) →
      RIn G (Set.range (fun i : ZMod 4 => (![z, v₁, v₂, x] : Fin 4 → V) i))ᶜ d.fst e.fst) := by
  have z0 : z ≠ v₀ := h0.ne.symm
  have z1 : z ≠ v₁ := h1.ne.symm
  have z2 : z ≠ v₂ := fun h => n02 (h ▸ h0)
  have z3 : z ≠ v₃ := fun h => n13 (h ▸ h1)
  have x0 : x ≠ v₀ := fun h => n02 (h ▸ hx2)
  have x1 : x ≠ v₁ := fun h => n13 (h ▸ hx3)
  have x2 : x ≠ v₂ := hx2.ne
  have x3 : x ≠ v₃ := hx3.ne
  have d01 := a01.ne; have d12 := a12.ne; have d23 := a23.ne; have d30 := a30.ne
  set c₁ := fun i : ZMod 4 => (![z, v₀, v₃, x] : Fin 4 → V) i with hc₁
  set c₂ := fun i : ZMod 4 => (![z, v₁, v₂, x] : Fin 4 → V) i with hc₂
  obtain ⟨cyc₁, -⟩ := c31_cyc4 h0.symm a30.symm hx3.symm hzx.symm n3 (fun h => nx0 h.symm) z3
    x0.symm
  obtain ⟨cyc₂, -⟩ := c31_cyc4 h1.symm a12 hx2.symm hzx.symm n2 (fun h => nx1 h.symm) z2
    x1.symm
  have ext₁ := extProp_four cyc₁.inj cyc₁.adj
  have ext₂ := extProp_four cyc₂.inj cyc₂.adj
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨d₁, f₁, hd₁, hf₁, hdf₁⟩, ⟨d₂, f₂, hd₂, hf₂, hdf₂⟩⟩ := hcon
  have m1 : ∀ u, u ∈ Set.range c₁ ↔ u = z ∨ u = v₀ ∨ u = v₃ ∨ u = x := fun u =>
    c31_mem_range_four
  have m2 : ∀ u, u ∈ Set.range c₂ ↔ u = z ∨ u = v₁ ∨ u = v₂ ∨ u = x := fun u =>
    c31_mem_range_four
  obtain ⟨B₂, t₂, hcl₂, v0B, v3B, ht₂, ht₂B⟩ := c31_side hG ext₂ hd₂ hf₂ hdf₂ a30.symm
    (by rw [m2]; simp [z0.symm, d01, ne02, x0.symm])
    (by rw [m2]; simp [z3.symm, ne13.symm, d23.symm, x3.symm])
  obtain ⟨B₁, t₁, hcl₁, v1B, v2B, ht₁, ht₁B⟩ := c31_side hG ext₁ hd₁ hf₁ hdf₁ a12
    (by rw [m1]; simp [z1.symm, d01.symm, ne13, x1.symm])
    (by rw [m1]; simp [z2.symm, ne02.symm, d23, x2.symm])
  have T1 : G.IsNClique 3 ({v₀, v₁, z} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨a01, h0, h1⟩
  have T2 : G.IsNClique 3 ({v₂, v₃, x} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨a23, hx2.symm, hx3.symm⟩
  have v0t : v₀ ∉ t₂ := fun h => v0B (ht₂B _ h)
  have v3t : v₃ ∉ t₂ := fun h => v3B (ht₂B _ h)
  have v1t : v₁ ∉ t₁ := fun h => v1B (ht₁B _ h)
  have v2t : v₂ ∉ t₁ := fun h => v2B (ht₁B _ h)
  have heq : t₁ = t₂ := by
    by_contra hne
    have := c31_four_le_triCount T1 T2 ht₂ ht₁
      (c31_ne_of_mem (u := v₀) (by simp) (by simp [ne02, d30.symm, x0.symm]))
      (c31_ne_of_mem (u := v₀) (by simp) v0t) (c31_ne_of_mem (u := v₁) (by simp) v1t)
      (c31_ne_of_mem (u := v₃) (by simp) v3t) (c31_ne_of_mem (u := v₂) (by simp) v2t)
      (Ne.symm hne)
    have := hG.tri
    omega
  subst heq
  obtain ⟨y, hyt, hyz, hyx⟩ : ∃ y ∈ t₁, y ≠ z ∧ y ≠ x := by
    by_contra hno
    push Not at hno
    have hsub : t₁ ⊆ {z, x} := fun y hy => by
      by_cases h : y = z
      · simp [h]
      · simp [hno y hy h]
    have := Finset.card_le_card hsub
    rw [ht₁.card_eq] at this
    have := Finset.card_le_two (a := z) (b := x)
    omega
  obtain ⟨u, hu⟩ := (G.degree_pos_iff_exists_adj y).1
    (by have := hG.isCritical4.three_le_degree y; omega)
  have hS : ∀ a ∈ ({z, x} : Set V), ∀ b ∈ ({z, x} : Set V), a ≠ b → G.Adj a b := by
    rintro a (rfl | rfl) b (rfl | rfl) hab
    · exact absurd rfl hab
    · exact hzx
    · exact hzx.symm
    · exact absurd rfl hab
  have hpath := hG.rIn_of_clique hS (d := ⟨(y, u), hu⟩) (e := ⟨(v₀, v₁), a01⟩)
    (by simp [hyz, hyx]) (by simp [z0.symm, x0.symm])
  simp only at hpath
  have key : ∀ w, RIn G ({z, x} : Set V)ᶜ y w →
      w ∈ B₁ ∧ w ∉ Set.range c₁ ∧ w ∈ B₂ ∧ w ∉ Set.range c₂ := by
    intro w hw
    induction hw with
    | refl =>
      refine ⟨ht₁B y hyt, ?_, ht₂B y hyt, ?_⟩
      · rw [m1]
        rintro (h | h | h | h)
        · exact hyz h
        · exact v0t (h ▸ hyt)
        · exact v3t (h ▸ hyt)
        · exact hyx h
      · rw [m2]
        rintro (h | h | h | h)
        · exact hyz h
        · exact v1t (h ▸ hyt)
        · exact v2t (h ▸ hyt)
        · exact hyx h
    | tail _ hstep ih =>
      obtain ⟨hab, -, hb⟩ := hstep
      obtain ⟨i1, i2, i3, i4⟩ := ih
      have hb1 := hcl₁ _ _ i1 i2 hab
      have hb2 := hcl₂ _ _ i3 i4 hab
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb
      refine ⟨hb1, ?_, hb2, ?_⟩
      · rw [m1]
        rintro (h | h | h | h)
        · exact hb.1 h
        · exact v0B (h ▸ hb2)
        · exact v3B (h ▸ hb2)
        · exact hb.2 h
      · rw [m2]
        rintro (h | h | h | h)
        · exact hb.1 h
        · exact v1B (h ▸ hb1)
        · exact v2B (h ▸ hb1)
        · exact hb.2 h
  exact (key v₀ hpath).2.1 ((m1 v₀).2 (Or.inr (Or.inl rfl)))

/-- **Case 3.1** (`x = y`): a 3-prism `v₀ v₁ z`, `v₂ v₃ x` whose 4-cycle `v₀ v₁ v₂ v₃` is a face.
-/
theorem GAMin.case31 (hG : GAMin G) (M : PlaneMap G) {e₀ e₁ e₂ e₃ : G.Dart}
    (hF : FourFace M e₀ e₁ e₂ e₃) {z x : V} (h0 : G.Adj e₀.fst z) (h1 : G.Adj e₁.fst z)
    (hzx : G.Adj z x) (hx2 : G.Adj x e₂.fst) (hx3 : G.Adj x e₃.fst) (n2 : ¬ G.Adj z e₂.fst)
    (n3 : ¬ G.Adj z e₃.fst) (nx0 : ¬ G.Adj x e₀.fst) (nx1 : ¬ G.Adj x e₁.fst) : False := by
  have a01 := hF.adj₀
  have a12 := hF.adj₁
  have a23 := hF.adj₂
  have a30 := hF.adj₃
  have n02 := hG.not_adj_of_fourFace M hF
  have n13 := hG.not_adj_of_fourFace M hF.rotate
  have ne02 := hF.ne02
  have ne13 := hF.ne13
  obtain ⟨m0, m1, m2, m3⟩ := hF.mem_faceVerts
  have r01 : M.rot e₀.symm = e₁ := (M.facePerm_apply e₀).symm.trans hF.f01
  have r12 : M.rot e₁.symm = e₂ := (M.facePerm_apply e₁).symm.trans hF.f12
  have r23 : M.rot e₂.symm = e₃ := (M.facePerm_apply e₂).symm.trans hF.f23
  have r30 : M.rot e₃.symm = e₀ := (M.facePerm_apply e₃).symm.trans hF.f30
  have z0 : z ≠ e₀.fst := h0.ne.symm
  have z1 : z ≠ e₁.fst := h1.ne.symm
  have z2 : z ≠ e₂.fst := fun h => n02 (h ▸ h0)
  have z3 : z ≠ e₃.fst := fun h => n13 (h ▸ h1)
  have x0 : x ≠ e₀.fst := fun h => n02 (h ▸ hx2)
  have x1 : x ≠ e₁.fst := fun h => n13 (h ▸ hx3)
  have x2 : x ≠ e₂.fst := hx2.ne
  have x3 : x ≠ e₃.fst := hx3.ne
  rcases c31_nonsep hG a01 a12 a23 a30 ne02 ne13 n02 n13 h0 h1 hzx hx2 hx3 n2 n3 nx0 nx1 with
    hc | hc
  · obtain ⟨cyc, ch⟩ := c31_cyc4 h0.symm a30.symm hx3.symm hzx.symm n3 (fun h => nx0 h.symm) z3
      x0.symm
    have hface := cycle_facial M (by norm_num) cyc ch hc
    have hPl := isPlanar_apexExtend_cycle M (by norm_num) cyc ch hc
    have hN0 := c31_nbr_of_rot M (w := e₀.fst) z3.symm z1.symm e₃.symm e₀ ⟨(e₀.fst, z), h0⟩
      hF.snd₃ rfl rfl rfl hF.snd₀ rfl r30
      (c31_tri_rot hG M h0 h1.symm a01 e₀ ⟨(e₀.fst, z), h0⟩ rfl hF.snd₀ rfl rfl)
      (c31_facial_rot M hface 1 ⟨(e₀.fst, z), h0⟩ e₃.symm rfl rfl hF.snd₃ rfl)
    have hN3 := c31_nbr_of_rot M (w := e₃.fst) x2.symm x0.symm e₂.symm e₃
      ⟨(e₃.fst, x), hx3.symm⟩ hF.snd₂ rfl rfl rfl hF.snd₃ rfl r23
      (c31_facial_rot M hface 2 e₃ ⟨(e₃.fst, x), hx3.symm⟩ rfl hF.snd₃ rfl rfl)
      (c31_tri_rot hG M a23.symm hx2.symm hx3.symm ⟨(e₃.fst, x), hx3.symm⟩ e₂.symm rfl rfl
        hF.snd₂ rfl)
    exact c31_core hG M e₀ hF.inj m1 m0 m3 m2 a01.symm a30.symm a23.symm a12.symm ne13 ne02
      n13 n02 h1 h0 hzx hx3 hx2 n3 n2 nx1 nx0 hPl (c31_mem_range_four.2 (Or.inl rfl))
      (c31_mem_range_four.2 (Or.inr (Or.inl rfl)))
      (c31_mem_range_four.2 (Or.inr (Or.inr (Or.inl rfl))))
      (c31_mem_range_four.2 (Or.inr (Or.inr (Or.inr rfl))))
      (fun u hu => (hN0 u hu).elim (fun h => Or.inr (Or.inl h))
        (fun h => h.elim Or.inl (fun h => Or.inr (Or.inr h))))
      (fun u hu => (hN3 u hu).elim (fun h => Or.inr (Or.inl h))
        (fun h => h.elim Or.inl (fun h => Or.inr (Or.inr h))))
  · obtain ⟨cyc, ch⟩ := c31_cyc4 h1.symm a12 hx2.symm hzx.symm n2 (fun h => nx1 h.symm) z2
      x1.symm
    have hface := cycle_facial M (by norm_num) cyc ch hc
    have hPl := isPlanar_apexExtend_cycle M (by norm_num) cyc ch hc
    have hN1 := c31_nbr_of_rot M (w := e₁.fst) z0.symm z2.symm e₀.symm e₁ ⟨(e₁.fst, z), h1⟩
      hF.snd₀ rfl rfl rfl hF.snd₁ rfl r01
      (c31_facial_rot M hface 1 ⟨(e₁.fst, z), h1⟩ e₁ rfl rfl rfl hF.snd₁).symm
      (c31_tri_rot hG M a01.symm h0 h1 ⟨(e₁.fst, z), h1⟩ e₀.symm rfl rfl hF.snd₀ rfl)
    have hN2 := c31_nbr_of_rot M (w := e₂.fst) x1.symm x3.symm e₁.symm e₂
      ⟨(e₂.fst, x), hx2.symm⟩ hF.snd₁ rfl rfl rfl hF.snd₂ rfl r12
      (c31_tri_rot hG M hx2.symm hx3 a23 e₂ ⟨(e₂.fst, x), hx2.symm⟩ rfl hF.snd₂ rfl rfl)
      (c31_facial_rot M hface 2 e₁.symm ⟨(e₂.fst, x), hx2.symm⟩ hF.snd₁ rfl rfl rfl).symm
    exact c31_core hG M e₀ hF.inj m0 m1 m2 m3 a01 a12 a23 a30 ne02 ne13 n02 n13 h0 h1 hzx hx2
      hx3 n2 n3 nx0 nx1 hPl (c31_mem_range_four.2 (Or.inl rfl))
      (c31_mem_range_four.2 (Or.inr (Or.inl rfl)))
      (c31_mem_range_four.2 (Or.inr (Or.inr (Or.inl rfl))))
      (c31_mem_range_four.2 (Or.inr (Or.inr (Or.inr rfl)))) hN1 hN2

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

/-! ### The theorem -/

theorem grunbaum_aksenov_aux : ∀ (n : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V),
    Fintype.card V + Nat.card G.edgeSet = n → IsPlanar G → triCount G ≤ 3 → G.Colorable 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ G hn hP ht
  by_contra hc
  exact GAMin.case3 ⟨hP, ht, hc, fun W _ H hlt hP' ht' => ih _ (hn ▸ hlt) W H rfl hP' ht'⟩

/-- **Grünbaum–Aksenov theorem.** A planar graph with at most three triangles is
3-colourable. -/
theorem grunbaum_aksenov (G : SimpleGraph V) (hP : IsPlanar G) (ht : triCount G ≤ 3) :
    G.Colorable 3 :=
  grunbaum_aksenov_aux _ V G rfl hP ht

end Grotzsch
