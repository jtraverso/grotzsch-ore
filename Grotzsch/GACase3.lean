/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Grotzsch.GACases
public import Grotzsch.Regions

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

/-! ### Case 3.2: cyclic order of the darts around a vertex -/

/-- `e` is the first dart satisfying `P` reached from `d` by rotating. -/
def NextIn (M : PlaneMap G) (P : G.Dart → Prop) (d e : G.Dart) : Prop :=
  ∃ n : ℕ, (M.rot ^ n) d = e ∧ P e ∧ ∀ m < n, ¬ P ((M.rot ^ m) d)

/-- Rotating from `a`, the dart `b` is reached before the dart `c`. -/
def RBefore (M : PlaneMap G) (a b c : G.Dart) : Prop := NextIn M (fun e => e = b ∨ e = c) a b

/-- The number of rotation steps from `a` to `b`. -/
def rpos (M : PlaneMap G) (a b : G.Dart) : ℕ :=
  if h : ∃ n : ℕ, (M.rot ^ n) a = b then Nat.find h else 0

omit [Fintype V] in
theorem rot_pow_fst' (M : PlaneMap G) (n : ℕ) (a : G.Dart) : ((M.rot ^ n) a).fst = a.fst := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, M.isRotationSystem.fst_apply, ih]

theorem c32_exists_pow (M : PlaneMap G) {a b : G.Dart} (h : a.fst = b.fst) :
    ∃ n : ℕ, (M.rot ^ n) a = b :=
  (M.isRotationSystem.sameCycle a b h).exists_nat_pow_eq

theorem rpos_spec (M : PlaneMap G) {a b : G.Dart} (h : a.fst = b.fst) :
    (M.rot ^ rpos M a b) a = b := by
  have hex := c32_exists_pow M h
  unfold rpos
  simp only [hex, ↓reduceDIte]
  exact Nat.find_spec hex

omit [Fintype V] in
theorem rpos_le (M : PlaneMap G) {a b : G.Dart} {n : ℕ} (h : (M.rot ^ n) a = b) :
    rpos M a b ≤ n := by
  have hex : ∃ n : ℕ, (M.rot ^ n) a = b := ⟨n, h⟩
  unfold rpos
  simp only [hex, ↓reduceDIte]
  exact Nat.find_min' hex h

omit [Fintype V] in
theorem rpos_self (M : PlaneMap G) (a : G.Dart) : rpos M a a = 0 :=
  Nat.le_zero.1 (rpos_le M (n := 0) rfl)

theorem rpos_inj (M : PlaneMap G) {a b c : G.Dart} (hb : a.fst = b.fst) (hc : a.fst = c.fst)
    (h : rpos M a b = rpos M a c) : b = c := by
  rw [← rpos_spec M hb, ← rpos_spec M hc, h]

theorem rpos_pos (M : PlaneMap G) {a b : G.Dart} (hb : a.fst = b.fst) (hne : b ≠ a) :
    0 < rpos M a b := by
  rcases Nat.eq_zero_or_pos (rpos M a b) with h | h
  · have := rpos_spec M hb
    rw [h, pow_zero, Perm.one_apply] at this
    exact absurd this.symm hne
  · exact h

theorem rpos_sub (M : PlaneMap G) {a b c : G.Dart} (hb : a.fst = b.fst) (hc : a.fst = c.fst)
    (hle : rpos M a b ≤ rpos M a c) : rpos M b c = rpos M a c - rpos M a b := by
  apply le_antisymm
  · apply rpos_le
    have hk := rpos_spec M hb
    have hj := rpos_spec M hc
    generalize rpos M a b = k at hk hle ⊢
    generalize rpos M a c = j at hj hle ⊢
    subst hk
    rw [← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hle, hj]
  · have h1 : (M.rot ^ (rpos M b c + rpos M a b)) a = c := by
      rw [pow_add, Perm.mul_apply, rpos_spec M hb, rpos_spec M (hb.symm.trans hc)]
    have := rpos_le M h1
    omega

theorem rpos_lt (M : PlaneMap G) {a b c : G.Dart} (hb : a.fst = b.fst) (hc : a.fst = c.fst)
    (hne : b ≠ a) : rpos M a c < rpos M b a + rpos M a b := by
  set P := rpos M b a + rpos M a b with hP
  have hper : (M.rot ^ P) a = a := by
    rw [hP, pow_add, Perm.mul_apply, rpos_spec M hb, rpos_spec M hb.symm]
  have hPpos : 0 < P := by have := rpos_pos M hb hne; omega
  by_contra hlt
  push Not at hlt
  have h1 : (M.rot ^ (rpos M a c - P)) a = c := by
    have hj := rpos_spec M hc
    generalize rpos M a c = j at hj hlt ⊢
    subst hj
    conv_rhs => rw [← Nat.sub_add_cancel hlt, pow_add, Perm.mul_apply, hper]
  have := rpos_le M h1
  omega

theorem rpos_rot (M : PlaneMap G) {a b : G.Dart} (hb : a.fst = b.fst) (hne : b ≠ a) :
    rpos M (M.rot a) b = rpos M a b - 1 := by
  have h0 := rpos_pos M hb hne
  apply le_antisymm
  · apply rpos_le
    rw [← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel h0, rpos_spec M hb]
  · have hb' : (M.rot a).fst = b.fst := (M.isRotationSystem.fst_apply a).trans hb
    have h1 : (M.rot ^ (rpos M (M.rot a) b + 1)) a = b := by
      rw [pow_succ, Perm.mul_apply, rpos_spec M hb']
    have := rpos_le M h1
    omega

theorem rBefore_iff (M : PlaneMap G) {a b c : G.Dart} (hb : a.fst = b.fst) (hc : a.fst = c.fst)
    (hbc : b ≠ c) : RBefore M a b c ↔ rpos M a b < rpos M a c := by
  constructor
  · rintro ⟨n, hn, -, hmin⟩
    have h1 : rpos M a b = n := by
      apply le_antisymm (rpos_le M hn)
      by_contra hlt
      push Not at hlt
      exact hmin _ hlt (Or.inl (rpos_spec M hb))
    have h2 : n ≤ rpos M a c := by
      by_contra hlt
      push Not at hlt
      exact hmin _ hlt (Or.inr (rpos_spec M hc))
    have h3 : rpos M a c ≠ n := fun h => hbc (by rw [← hn, ← h, rpos_spec M hc])
    omega
  · intro hlt
    refine ⟨rpos M a b, rpos_spec M hb, Or.inl rfl, fun m hm hP => ?_⟩
    rcases hP with h | h
    · have := rpos_le M h; omega
    · have := rpos_le M h; omega

/-! Cyclic-order rules. -/

theorem rBefore_total (M : PlaneMap G) {a b c : G.Dart} (hb : a.fst = b.fst) (hc : a.fst = c.fst)
    (hbc : b ≠ c) : RBefore M a b c ∨ RBefore M a c b := by
  rw [rBefore_iff M hb hc hbc, rBefore_iff M hc hb hbc.symm]
  have : rpos M a b ≠ rpos M a c := fun h => hbc (rpos_inj M hb hc h)
  omega

theorem rBefore_asymm (M : PlaneMap G) {a b c : G.Dart} (hb : a.fst = b.fst) (hc : a.fst = c.fst)
    (hbc : b ≠ c) (h1 : RBefore M a b c) (h2 : RBefore M a c b) : False := by
  rw [rBefore_iff M hb hc hbc] at h1
  rw [rBefore_iff M hc hb hbc.symm] at h2
  omega

theorem rBefore_cyc (M : PlaneMap G) {a b c : G.Dart} (hb : a.fst = b.fst) (hc : a.fst = c.fst)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h : RBefore M a b c) : RBefore M b c a := by
  rw [rBefore_iff M hb hc hbc] at h
  rw [rBefore_iff M (hb.symm.trans hc) hb.symm hac.symm,
    rpos_sub M hb hc h.le]
  have := rpos_lt M hb hc (Ne.symm hab)
  omega

theorem rBefore_trans (M : PlaneMap G) {a b c d : G.Dart} (hb : a.fst = b.fst)
    (hc : a.fst = c.fst) (hd : a.fst = d.fst) (hbc : b ≠ c) (hcd : c ≠ d) (hbd : b ≠ d)
    (h1 : RBefore M a b c) (h2 : RBefore M a c d) : RBefore M a b d := by
  rw [rBefore_iff M hb hc hbc] at h1
  rw [rBefore_iff M hc hd hcd] at h2
  rw [rBefore_iff M hb hd hbd]
  omega

theorem rBefore_rot (M : PlaneMap G) {a b c : G.Dart} (hb : a.fst = b.fst) (hc : a.fst = c.fst)
    (hab : b ≠ a) (hac : c ≠ a) (hbc : b ≠ c) : RBefore M (M.rot a) b c ↔ RBefore M a b c := by
  have ha' : (M.rot a).fst = a.fst := M.isRotationSystem.fst_apply a
  rw [rBefore_iff M hb hc hbc, rBefore_iff M (ha'.trans hb) (ha'.trans hc) hbc,
    rpos_rot M hb hab, rpos_rot M hc hac]
  have := rpos_pos M hb hab
  have := rpos_pos M hc hac
  omega

theorem rBefore_self (M : PlaneMap G) {a c : G.Dart} (hc : a.fst = c.fst) (hac : a ≠ c) :
    RBefore M a a c := by
  rw [rBefore_iff M rfl hc hac, rpos_self]
  exact rpos_pos M hc (Ne.symm hac)


omit [Fintype V] in
theorem rBefore_of_rot (M : PlaneMap G) {a b c : G.Dart} (h : M.rot a = b)
    (hab : a ≠ b) (hac : a ≠ c) : RBefore M a b c :=
  ⟨1, by rw [pow_one, h], Or.inl rfl, fun m hm hP => by
    obtain rfl : m = 0 := by omega
    rcases hP with h' | h'
    · exact hab h'
    · exact hac h'⟩

/-! ### First darts of a predicate -/

omit [Fintype V] in
theorem nextIn_unique (M : PlaneMap G) {P : G.Dart → Prop} {d e e' : G.Dart}
    (h : NextIn M P d e) (h' : NextIn M P d e') : e = e' := by
  obtain ⟨n, hn, hP, hmin⟩ := h
  obtain ⟨n', hn', hP', hmin'⟩ := h'
  have : n = n' := by
    rcases lt_trichotomy n n' with h | h | h
    · exact (hmin' n h (hn ▸ hP)).elim
    · exact h
    · exact (hmin n' h (hn' ▸ hP')).elim
  subst this
  exact hn.symm.trans hn'

omit [Fintype V] in
theorem nextIn_fst (M : PlaneMap G) {P : G.Dart → Prop} {d e : G.Dart} (h : NextIn M P d e) :
    e.fst = d.fst := by
  obtain ⟨n, hn, -⟩ := h
  rw [← hn, rot_pow_fst']

omit [Fintype V] in
theorem nextIn_congr (M : PlaneMap G) {P Q : G.Dart → Prop} {d e : G.Dart}
    (h : ∀ g : G.Dart, g.fst = d.fst → (P g ↔ Q g)) : NextIn M P d e ↔ NextIn M Q d e := by
  constructor
  · rintro ⟨n, hn, hP, hmin⟩
    refine ⟨n, hn, (h e (hn ▸ rot_pow_fst' M n d)).1 hP, fun m hm hQ => hmin m hm ?_⟩
    exact (h _ (rot_pow_fst' M m d)).2 hQ
  · rintro ⟨n, hn, hP, hmin⟩
    refine ⟨n, hn, (h e (hn ▸ rot_pow_fst' M n d)).2 hP, fun m hm hQ => hmin m hm ?_⟩
    exact (h _ (rot_pow_fst' M m d)).1 hQ

theorem nextIn_exists (M : PlaneMap G) {P : G.Dart → Prop} {d g : G.Dart} (hg : g.fst = d.fst)
    (hP : P g) : ∃ e, NextIn M P d e := by
  obtain ⟨n, hn⟩ := c32_exists_pow M hg.symm
  have hex : ∃ n : ℕ, P ((M.rot ^ n) d) := ⟨n, hn ▸ hP⟩
  exact ⟨_, Nat.find hex, rfl, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩

omit [Fintype V] in
theorem nextIn_self (M : PlaneMap G) {P : G.Dart → Prop} {d : G.Dart} (h : P d) :
    NextIn M P d d :=
  ⟨0, rfl, h, fun m hm => absurd hm (Nat.not_lt_zero m)⟩

omit [Fintype V] in
theorem nextIn_of_rot (M : PlaneMap G) {P : G.Dart → Prop} {d e : G.Dart} (hd : ¬ P d)
    (h : NextIn M P (M.rot d) e) : NextIn M P d e := by
  obtain ⟨n, hn, hP, hmin⟩ := h
  refine ⟨n + 1, by rw [pow_succ, Perm.mul_apply, hn], hP, fun m hm hm' => ?_⟩
  rcases m with _ | m
  · exact hd hm'
  · exact hmin m (by omega) (by rwa [pow_succ, Perm.mul_apply] at hm')

/-- With exactly two `P`-darts `p ≠ q` at a vertex, if every dart that is not a `P`-dart sees `q`
first, then the rotation takes `p` to `q`. -/
theorem rot_eq_of_nextIn (M : PlaneMap G) {P : G.Dart → Prop} {p q : G.Dart}
    (hpq : p.fst = q.fst) (hne : p ≠ q) (hP : P q)
    (htwo : ∀ g : G.Dart, g.fst = p.fst → P g → g = p ∨ g = q)
    (hno : ∀ e f : G.Dart, e.fst = p.fst → ¬ P e → NextIn M P e f → f = p) : M.rot p = q := by
  have hr : (M.rot p).fst = p.fst := M.isRotationSystem.fst_apply p
  by_cases hPr : P (M.rot p)
  · rcases htwo _ hr hPr with h | h
    · exfalso
      have hpow : ∀ n : ℕ, (M.rot ^ n) p = p := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ', Perm.mul_apply, ih, h]
      obtain ⟨n, hn⟩ := c32_exists_pow M hpq
      exact hne ((hpow n).symm.trans hn)
    · exact h
  · exfalso
    obtain ⟨f, hf⟩ := nextIn_exists M (P := P) (d := M.rot p) (g := q) (hr.trans hpq).symm hP
    have hfp := hno _ _ hr hPr hf
    subst hfp
    obtain ⟨n, hn, -, hmin⟩ := hf
    have hj := rpos_spec M hpq
    have hj0 := rpos_pos M hpq (Ne.symm hne)
    have hle : n + 1 ≤ rpos M f q := by
      by_contra hlt
      push Not at hlt
      have := hmin (rpos M f q - 1) (by omega)
      rw [← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hj0, hj] at this
      exact this hP
    have hper : (M.rot ^ (n + 1)) f = f := by rw [pow_succ, Perm.mul_apply, hn]
    have h1 : (M.rot ^ (rpos M f q - (n + 1))) f = q := by
      generalize rpos M f q = j at hj hle hj0 ⊢
      subst hj
      conv_rhs => rw [← Nat.sub_add_cancel hle, pow_add, Perm.mul_apply, hper]
    have := rpos_le M h1
    omega


/-! ### Four-cycles -/

omit [Fintype V] in
/-- A 4-cycle `a b c d` of `G`. -/
structure Cyc4 (G : SimpleGraph V) (a b c d : V) : Prop where
  ab : a ≠ b
  ac : a ≠ c
  ad : a ≠ d
  bc : b ≠ c
  bd : b ≠ d
  cd : c ≠ d
  hab : G.Adj a b
  hbc : G.Adj b c
  hcd : G.Adj c d
  hda : G.Adj d a

omit [Fintype V] in
theorem Cyc4.rot {a b c d : V} (h : Cyc4 G a b c d) : Cyc4 G b c d a :=
  ⟨h.bc, h.bd, h.ab.symm, h.cd, h.ac.symm, h.ad.symm, h.hbc, h.hcd, h.hda, h.hab⟩

omit [Fintype V] in
theorem Cyc4.rev {a b c d : V} (h : Cyc4 G a b c d) : Cyc4 G d c b a :=
  ⟨h.cd.symm, h.bd.symm, h.ad.symm, h.bc.symm, h.ac.symm, h.ab.symm, h.hcd.symm, h.hbc.symm,
    h.hab.symm, h.hda.symm⟩

omit [Fintype V] in
/-- `(p, q)` is a forward step of the 4-cycle `a b c d`. -/
def fw4 (a b c d p q : V) : Prop :=
  (p = a ∧ q = b) ∨ (p = b ∧ q = c) ∨ (p = c ∧ q = d) ∨ (p = d ∧ q = a)

omit [Fintype V] in
/-- `(p, q)` is a step of the 4-cycle `a b c d` in either direction. -/
def cy4 (a b c d p q : V) : Prop := fw4 a b c d p q ∨ fw4 d c b a p q

omit [Fintype V] in
theorem fw4_rot (a b c d : V) : fw4 a b c d = fw4 b c d a := by
  funext p q; unfold fw4; apply propext; tauto

omit [Fintype V] in
theorem cy4_rot (a b c d : V) : cy4 a b c d = cy4 b c d a := by
  funext p q; unfold cy4 fw4; apply propext; tauto

omit [Fintype V] in
theorem cy4_rev (a b c d : V) : cy4 a b c d = cy4 d c b a := by
  funext p q; unfold cy4 fw4; apply propext; tauto

omit [Fintype V] in
theorem set4_rot (a b c d : V) : ({a, b, c, d} : Set V) = {b, c, d, a} := by
  ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

omit [Fintype V] in
theorem set4_rev (a b c d : V) : ({a, b, c, d} : Set V) = {d, c, b, a} := by
  ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

omit [Fintype V] in
theorem Cyc4.cy4_at {a b c d : V} (h : Cyc4 G a b c d) {q : V} :
    cy4 a b c d a q ↔ q = b ∨ q = d := by
  have := h.ab; have := h.ac; have := h.ad
  have := h.ab.symm; have := h.ac.symm; have := h.ad.symm
  unfold cy4 fw4
  constructor
  · intro hq; rcases hq with (h1 | h1 | h1 | h1) | (h1 | h1 | h1 | h1) <;> simp_all
  · rintro (rfl | rfl) <;> simp

omit [Fintype V] in
theorem Cyc4.fw4_at {a b c d : V} (h : Cyc4 G a b c d) {q : V} :
    fw4 a b c d a q ↔ q = b := by
  have := h.ab; have := h.ac; have := h.ad
  have := h.ab.symm; have := h.ac.symm; have := h.ad.symm
  unfold fw4
  constructor
  · intro hq; rcases hq with h1 | h1 | h1 | h1 <;> simp_all
  · rintro rfl; simp

omit [Fintype V] in
theorem Cyc4.fw4_rev_at {a b c d : V} (h : Cyc4 G a b c d) {q : V} :
    fw4 d c b a a q ↔ q = d := by
  have := h.ab; have := h.ac; have := h.ad
  have := h.ab.symm; have := h.ac.symm; have := h.ad.symm
  unfold fw4
  constructor
  · intro hq; rcases hq with h1 | h1 | h1 | h1 <;> simp_all
  · rintro rfl; simp

omit [Fintype V] in
theorem Cyc4.not_fw4_both {a b c d : V} (h : Cyc4 G a b c d) {p q : V}
    (h1 : fw4 a b c d p q) (h2 : fw4 d c b a p q) : False := by
  have := h.ab; have := h.ac; have := h.ad; have := h.bc; have := h.bd; have := h.cd
  have := h.ab.symm; have := h.ac.symm; have := h.ad.symm; have := h.bc.symm
  have := h.bd.symm; have := h.cd.symm
  unfold fw4 at h1 h2
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all

omit [Fintype V] in
theorem Cyc4.cy4_step {a b c d : V} (h : Cyc4 G a b c d) {p q r : V} (h1 : cy4 a b c d p q)
    (h2 : cy4 a b c d q r) (h3 : r ≠ p) : fw4 a b c d p q ↔ fw4 a b c d q r := by
  have := h.ab; have := h.ac; have := h.ad; have := h.bc; have := h.bd; have := h.cd
  have := h.ab.symm; have := h.ac.symm; have := h.ad.symm; have := h.bc.symm
  have := h.bd.symm; have := h.cd.symm
  unfold cy4 fw4 at *
  rcases h1 with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
    (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
  rcases h2 with (⟨h4, rfl⟩ | ⟨h4, rfl⟩ | ⟨h4, rfl⟩ | ⟨h4, rfl⟩) |
    (⟨h4, rfl⟩ | ⟨h4, rfl⟩ | ⟨h4, rfl⟩ | ⟨h4, rfl⟩) <;> simp_all

omit [Fintype V] in
theorem Cyc4.cy4_other {a b c d : V} (h : Cyc4 G a b c d) {p q : V} (h1 : cy4 a b c d p q) :
    ∃ r, cy4 a b c d p r ∧ r ≠ q := by
  have := h.ab; have := h.ac; have := h.ad; have := h.bc; have := h.bd; have := h.cd
  have := h.ab.symm; have := h.ac.symm; have := h.ad.symm; have := h.bc.symm
  have := h.bd.symm; have := h.cd.symm
  unfold cy4 fw4 at *
  rcases h1 with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
    (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact ⟨d, by simp, by simp_all⟩
  · exact ⟨a, by simp, by simp_all⟩
  · exact ⟨b, by simp, by simp_all⟩
  · exact ⟨c, by simp, by simp_all⟩
  · exact ⟨a, by simp, by simp_all⟩
  · exact ⟨d, by simp, by simp_all⟩
  · exact ⟨c, by simp, by simp_all⟩
  · exact ⟨b, by simp, by simp_all⟩

omit [Fintype V] in
theorem Cyc4.cy4_adj {a b c d : V} (h : Cyc4 G a b c d) {p q : V} (h1 : cy4 a b c d p q) :
    G.Adj p q := by
  unfold cy4 fw4 at h1
  rcases h1 with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
    (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact h.hab
  · exact h.hbc
  · exact h.hcd
  · exact h.hda
  · exact h.hcd.symm
  · exact h.hbc.symm
  · exact h.hab.symm
  · exact h.hda.symm

omit [Fintype V] in
theorem cy4_mem {a b c d p q : V} (h1 : cy4 a b c d p q) :
    p ∈ ({a, b, c, d} : Set V) ∧ q ∈ ({a, b, c, d} : Set V) := by
  unfold cy4 fw4 at h1
  rcases h1 with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
    (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

omit [Fintype V] in
theorem cy4_symm {a b c d p q : V} (h1 : cy4 a b c d p q) : cy4 a b c d q p := by
  unfold cy4 fw4 at *; tauto

omit [Fintype V] in
theorem exists_cy4 {a b c d p : V} (hp : p ∈ ({a, b, c, d} : Set V)) : ∃ q, cy4 a b c d p q := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  unfold cy4 fw4
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨b, by simp⟩
  · exact ⟨c, by simp⟩
  · exact ⟨d, by simp⟩
  · exact ⟨a, by simp⟩


omit [Fintype V] in
/-- Forward darts of the 4-cycle `a b c d`. -/
def Fw4 (a b c d : V) (e : G.Dart) : Prop := fw4 a b c d e.fst e.snd

omit [Fintype V] in
/-- Darts of the 4-cycle `a b c d`. -/
def Cy4 (a b c d : V) (e : G.Dart) : Prop := cy4 a b c d e.fst e.snd

omit [Fintype V] in
/-- The 4-cycle `a b c d` as a graph. -/
def cyc4G (a b c d : V) : SimpleGraph V where
  Adj p q := p ≠ q ∧ cy4 a b c d p q
  symm := ⟨fun _ _ h => ⟨h.1.symm, cy4_symm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

omit [Fintype V] in
theorem Cyc4.le_cyc4G {a b c d : V} (h : Cyc4 G a b c d) : cyc4G a b c d ≤ G :=
  fun _ _ hpq => h.cy4_adj hpq.2

omit [Fintype V] in
theorem inH_cyc4G_iff {a b c d : V} (e : G.Dart) :
    InH (cyc4G a b c d) e ↔ Cy4 a b c d e :=
  ⟨fun h' => h'.2, fun h' => ⟨e.adj.ne, h'⟩⟩

omit [Fintype V] in
theorem Cyc4.subVerts_eq {a b c d : V} (h : Cyc4 G a b c d) :
    subVerts (cyc4G a b c d) = ({a, b, c, d} : Set V) := by
  ext p
  constructor
  · rintro ⟨q, hq⟩
    exact (cy4_mem hq.2).1
  · intro hp
    obtain ⟨q, hq⟩ := exists_cy4 hp
    exact ⟨q, (h.cy4_adj hq).ne, hq⟩

omit [Fintype V] in
theorem Cyc4.reachable {a b c d : V} (h : Cyc4 G a b c d) :
    ∀ p ∈ subVerts (cyc4G a b c d), ∀ q ∈ subVerts (cyc4G a b c d),
      (cyc4G a b c d).Reachable p q := by
  have hab : (cyc4G a b c d).Adj a b := ⟨h.ab, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
  have hbc : (cyc4G a b c d).Adj b c := ⟨h.bc, Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
  have hcd : (cyc4G a b c d).Adj c d := ⟨h.cd, Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
  have ha : ∀ p ∈ subVerts (cyc4G a b c d), (cyc4G a b c d).Reachable a p := by
    intro p hp
    rw [h.subVerts_eq] at hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · rfl
    · exact hab.reachable
    · exact hab.reachable.trans hbc.reachable
    · exact (hab.reachable.trans hbc.reachable).trans hcd.reachable
  intro p hp q hq
  exact (ha p hp).symm.trans (ha q hq)

omit [Fintype V] in
theorem Cyc4.dart_at {a b c d : V} (h : Cyc4 G a b c d) {g : G.Dart} (hg : g.fst = a) :
    Cy4 a b c d g ↔ g = ⟨(a, b), h.hab⟩ ∨ g = ⟨(a, d), h.hda.symm⟩ := by
  unfold Cy4
  rw [hg, h.cy4_at]
  constructor
  · rintro (h1 | h1)
    · exact Or.inl (dart_eq_of hg h1)
    · exact Or.inr (dart_eq_of hg h1)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

omit [Fintype V] in
theorem Cyc4.fw_at {a b c d : V} (h : Cyc4 G a b c d) {g : G.Dart} (hg : g.fst = a) :
    Fw4 a b c d g ↔ g = ⟨(a, b), h.hab⟩ := by
  unfold Fw4
  rw [hg, h.fw4_at]
  constructor
  · intro h1; exact dart_eq_of hg h1
  · rintro rfl; rfl

omit [Fintype V] in
theorem Cyc4.fw_rev_at {a b c d : V} (h : Cyc4 G a b c d) {g : G.Dart} (hg : g.fst = a) :
    Fw4 d c b a g ↔ g = ⟨(a, d), h.hda.symm⟩ := by
  unfold Fw4
  rw [hg, h.fw4_rev_at]
  constructor
  · intro h1; exact dart_eq_of hg h1
  · rintro rfl; rfl

/-- The induced rotation on a 4-cycle never fixes a dart. -/
theorem Cyc4.subRot_ne {a b c d : V} (h : Cyc4 G a b c d) (M : PlaneMap G)
    (g : (cyc4G a b c d).Dart) : subRot M h.le_cyc4G g ≠ g := by
  intro hfix
  obtain ⟨r, hr, hrne⟩ := h.cy4_other g.adj.2
  let g' : (cyc4G a b c d).Dart := ⟨(g.fst, r), (h.cy4_adj hr).ne, hr⟩
  obtain ⟨i, hi⟩ := (isRotationSystem_subRot M h.le_cyc4G).sameCycle g g' rfl
  rw [Perm.zpow_apply_eq_self_of_apply_eq_self hfix] at hi
  exact hrne (congrArg (fun x : (cyc4G a b c d).Dart => x.snd) hi).symm

theorem Cyc4.fw_facePerm {a b c d : V} (h : Cyc4 G a b c d) (M : PlaneMap G)
    (g : (cyc4G a b c d).Dart) :
    Fw4 a b c d (toDart h.le_cyc4G g) ↔
      Fw4 a b c d (toDart h.le_cyc4G ((restrictMap M h.le_cyc4G).facePerm g)) := by
  rw [PlaneMap.facePerm_apply]
  set k := (restrictMap M h.le_cyc4G).rot g.symm with hk
  have hk1 : k.fst = g.snd := (isRotationSystem_subRot M h.le_cyc4G).fst_apply g.symm
  have hk2 : k.snd ≠ g.fst := by
    intro he
    exact h.subRot_ne M g.symm (dart_eq_of hk1 he)
  have hk3 : cy4 a b c d k.fst k.snd := k.adj.2
  rw [hk1] at hk3
  show fw4 a b c d g.fst g.snd ↔ fw4 a b c d k.fst k.snd
  rw [hk1]
  exact h.cy4_step g.adj.2 hk3 hk2

theorem Cyc4.fw_sameCycle {a b c d : V} (h : Cyc4 G a b c d) (M : PlaneMap G)
    {g g' : (cyc4G a b c d).Dart} (hs : SameCycle (restrictMap M h.le_cyc4G).facePerm g g')
    (hg : Fw4 a b c d (toDart h.le_cyc4G g)) : Fw4 a b c d (toDart h.le_cyc4G g') := by
  obtain ⟨i, rfl⟩ := hs
  induction i using Int.induction_on with
  | zero => simpa using hg
  | succ i ih =>
    rw [add_comm, zpow_add, zpow_one, Perm.mul_apply]
    exact (h.fw_facePerm M _).1 ih
  | pred i ih =>
    rw [(h.fw_facePerm M _), ← Perm.mul_apply, ← zpow_one_add]
    simpa using ih

/-- **Jordan for 4-cycles** (from R1): darts leading into one component of `G - C` lie on the same
side of the 4-cycle `C`. -/
theorem Cyc4.r1 {a b c d : V} (h : Cyc4 G a b c d) (M : PlaneMap G) {e₁ e₂ f₁ f₂ : G.Dart}
    (h1 : e₁.fst ∈ ({a, b, c, d} : Set V)) (h2 : e₂.fst ∈ ({a, b, c, d} : Set V))
    (h1' : e₁.snd ∉ ({a, b, c, d} : Set V)) (h2' : e₂.snd ∉ ({a, b, c, d} : Set V))
    (hr : RIn G ({a, b, c, d} : Set V)ᶜ e₁.snd e₂.snd)
    (n1 : NextIn M (Cy4 a b c d) e₁ f₁) (n2 : NextIn M (Cy4 a b c d) e₂ f₂)
    (hf : Fw4 a b c d f₁) : Fw4 a b c d f₂ := by
  have hH := h.le_cyc4G
  rw [← h.subVerts_eq] at h1 h2 h1' h2' hr
  have conv : ∀ {e f : G.Dart}, NextIn M (Cy4 a b c d) e f →
      ∃ g : (cyc4G a b c d).Dart, toDart hH g = f ∧ IsNextH M hH e g := by
    intro e f hn
    obtain ⟨n, hn, hP, hmin⟩ := hn
    refine ⟨⟨f.toProd, (inH_cyc4G_iff f).2 hP⟩, rfl, n, hn, fun m hm hm' => ?_⟩
    exact hmin m hm ((inH_cyc4G_iff _).1 hm')
  obtain ⟨g₁, rfl, hg₁⟩ := conv n1
  obtain ⟨g₂, rfl, hg₂⟩ := conv n2
  exact h.fw_sameCycle M (sameCycle_of_rIn M hH h.reachable h1 h2 h1' h2' hr hg₁ hg₂) hf


omit [Fintype V] in
theorem Cy4_rot (a b c d : V) : (Cy4 a b c d : G.Dart → Prop) = Cy4 b c d a := by
  funext e; unfold Cy4; rw [cy4_rot]

omit [Fintype V] in
theorem Cy4_rev (a b c d : V) : (Cy4 a b c d : G.Dart → Prop) = Cy4 d c b a := by
  funext e; unfold Cy4; rw [cy4_rev]

omit [Fintype V] in
theorem Fw4_rot (a b c d : V) : (Fw4 a b c d : G.Dart → Prop) = Fw4 b c d a := by
  funext e; unfold Fw4; rw [fw4_rot]

/-- `w` lies off the 4-cycle `a b c d`, on its forward side. -/
def In4 (M : PlaneMap G) (a b c d w : V) : Prop :=
  w ∉ ({a, b, c, d} : Set V) ∧ ∃ e f : G.Dart, e.fst ∈ ({a, b, c, d} : Set V) ∧
    e.snd ∉ ({a, b, c, d} : Set V) ∧ NextIn M (Cy4 a b c d) e f ∧ Fw4 a b c d f ∧
    RIn G ({a, b, c, d} : Set V)ᶜ e.snd w

omit [Fintype V] in
theorem in4_rot (M : PlaneMap G) (a b c d : V) : In4 M a b c d = In4 M b c d a := by
  funext w; unfold In4; rw [set4_rot, Cy4_rot, Fw4_rot]

omit [Fintype V] in
theorem in4_not_mem {M : PlaneMap G} {a b c d w : V} (h : In4 M a b c d w) :
    w ∉ ({a, b, c, d} : Set V) := h.1

omit [Fintype V] in
theorem in4_of_rIn {M : PlaneMap G} {a b c d w u : V} (h : In4 M a b c d w)
    (hr : RIn G ({a, b, c, d} : Set V)ᶜ w u) : In4 M a b c d u := by
  obtain ⟨hw, e, f, h1, h2, h3, h4, h5⟩ := h
  exact ⟨hr.mem hw, e, f, h1, h2, h3, h4, h5.trans hr⟩

omit [Fintype V] in
theorem in4_of_adj {M : PlaneMap G} {a b c d w u : V} (h : In4 M a b c d w) (hwu : G.Adj w u)
    (hu : u ∉ ({a, b, c, d} : Set V)) : In4 M a b c d u :=
  in4_of_rIn h (RIn.single hwu h.1 hu)

omit [Fintype V] in
theorem Cyc4.nextIn_at {a b c d : V} (h : Cyc4 G a b c d) (M : PlaneMap G) {e f : G.Dart}
    (he : e.fst = a) : NextIn M (Cy4 a b c d) e f ↔
      NextIn M (fun g => g = ⟨(a, b), h.hab⟩ ∨ g = ⟨(a, d), h.hda.symm⟩) e f :=
  nextIn_congr M fun _ hg => h.dart_at (hg.trans he)

omit [Fintype V] in
theorem Cyc4.in4_of_rBefore {a b c d : V} (h : Cyc4 G a b c d) (M : PlaneMap G) {e : G.Dart}
    (he : e.fst = a) (he' : e.snd ∉ ({a, b, c, d} : Set V))
    (hb : RBefore M e ⟨(a, b), h.hab⟩ ⟨(a, d), h.hda.symm⟩) : In4 M a b c d e.snd :=
  ⟨he', e, ⟨(a, b), h.hab⟩, by rw [he]; simp, he', (h.nextIn_at M he).2 hb,
    (h.fw_at rfl).2 rfl, RIn.refl _⟩

theorem Cyc4.rBefore_of_in4 {a b c d : V} (h : Cyc4 G a b c d) (M : PlaneMap G) {q : V}
    (hq : In4 M a b c d q) (haq : G.Adj a q) :
    RBefore M ⟨(a, q), haq⟩ ⟨(a, b), h.hab⟩ ⟨(a, d), h.hda.symm⟩ := by
  obtain ⟨hqS, e, f, he1, he2, hn, hf, hr⟩ := hq
  obtain ⟨f', hf'⟩ := nextIn_exists M (P := Cy4 a b c d) (d := ⟨(a, q), haq⟩)
    (g := ⟨(a, b), h.hab⟩) rfl ((h.dart_at rfl).2 (Or.inl rfl))
  have hfw := h.r1 M he1 (by simp) he2 hqS hr hn hf' hf
  have hfa : f'.fst = a := nextIn_fst M hf'
  rw [h.fw_at hfa] at hfw
  subst hfw
  exact (h.nextIn_at M rfl).1 hf'

theorem Cyc4.in4_disj {a b c d : V} (h : Cyc4 G a b c d) (M : PlaneMap G) {w : V}
    (h1 : In4 M a b c d w) (h2 : In4 M d c b a w) : False := by
  obtain ⟨hw, e, f, he1, he2, hn, hf, hr⟩ := h1
  obtain ⟨-, e', f', he1', he2', hn', hf', hr'⟩ := h2
  rw [← set4_rev] at he1' he2' hr'
  rw [← Cy4_rev] at hn'
  exact h.not_fw4_both (h.r1 M he1 he1' he2 he2' (hr.trans hr'.symm) hn hn' hf) hf'

theorem Cyc4.in4_total {a b c d : V} (h : Cyc4 G a b c d) (M : PlaneMap G) {w s : V}
    (hw : w ∉ ({a, b, c, d} : Set V)) (hs : s ∈ ({a, b, c, d} : Set V))
    (hconn : RIn G Set.univ w s) : In4 M a b c d w ∨ In4 M d c b a w := by
  obtain ⟨p, q, hwp, -, hp, -, hq, hpq⟩ :=
    hconn.exit (P := ({a, b, c, d} : Set V)ᶜ) hw (fun h' => h' hs)
  simp only [Set.mem_compl_iff, not_not] at hq
  obtain ⟨r, hr⟩ := exists_cy4 hq
  obtain ⟨f, hf⟩ := nextIn_exists M (P := Cy4 a b c d) (d := ⟨(q, p), hpq.symm⟩)
    (g := ⟨(q, r), h.cy4_adj hr⟩) rfl hr
  have hpw : RIn G ({a, b, c, d} : Set V)ᶜ p w :=
    (hwp.mono_set fun x hx => hx.2).symm
  have hP : Cy4 a b c d f := by obtain ⟨_, _, h', _⟩ := hf; exact h'
  rcases hP with hfw | hfw
  · exact Or.inl (in4_of_rIn ⟨hp, ⟨(q, p), hpq.symm⟩, f, hq, hp, hf, hfw, RIn.refl _⟩ hpw)
  · right
    rw [set4_rev] at hp hq hpw
    rw [Cy4_rev] at hf
    exact in4_of_rIn ⟨hp, ⟨(q, p), hpq.symm⟩, f, hq, hp, hf, hfw, RIn.refl _⟩ hpw


/-- If the forward side of a 4-cycle is empty and `a c` is not an edge, the rotation at `a` turns
the backward dart into the forward one. -/
theorem Cyc4.rot_eq_of_empty {a b c d : V} (h : Cyc4 G a b c d) (M : PlaneMap G)
    (nac : ¬ G.Adj a c) (hno : ∀ w, ¬ In4 M a b c d w) :
    M.rot ⟨(a, d), h.hda.symm⟩ = ⟨(a, b), h.hab⟩ := by
  refine rot_eq_of_nextIn M (P := Cy4 a b c d) rfl (fun he => h.bd.symm
    (congrArg (fun g : G.Dart => g.snd) he)) ((h.dart_at rfl).2 (Or.inl rfl))
    (fun g hg hP => ((h.dart_at hg).1 hP).symm) (fun e f he hPe hf => ?_)
  have hfa : f.fst = a := (nextIn_fst M hf).trans he
  have hPf : Cy4 a b c d f := by obtain ⟨_, _, h', _⟩ := hf; exact h'
  rcases (h.dart_at hfa).1 hPf with rfl | rfl
  · exfalso
    have he' : e.snd ∉ ({a, b, c, d} : Set V) := by
      intro hm
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      have hadj := e.adj
      rw [he] at hadj
      rcases hm with h1 | h1 | h1 | h1
      · exact hadj.ne h1.symm
      · exact hPe ((h.dart_at he).2 (Or.inl (dart_eq_of he h1)))
      · exact nac (h1 ▸ hadj)
      · exact hPe ((h.dart_at he).2 (Or.inr (dart_eq_of he h1)))
    exact hno _ ⟨he', e, _, by rw [he]; simp, he', hf, (h.fw_at rfl).2 rfl, RIn.refl _⟩
  · rfl

omit [Fintype V] in
theorem fourFace_of_facePerm (M : PlaneMap G) {d₀ d₁ d₂ d₃ : G.Dart}
    (f01 : M.facePerm d₀ = d₁) (f12 : M.facePerm d₁ = d₂) (f23 : M.facePerm d₂ = d₃)
    (f30 : M.facePerm d₃ = d₀) (ne02 : d₀.fst ≠ d₂.fst) (ne13 : d₁.fst ≠ d₃.fst) :
    FourFace M d₀ d₁ d₂ d₃ := by
  have i1 : M.facePerm⁻¹ d₁ = d₀ := by rw [Perm.inv_eq_iff_eq]; exact f01.symm
  have i2 : M.facePerm⁻¹ d₂ = d₁ := by rw [Perm.inv_eq_iff_eq]; exact f12.symm
  have i3 : M.facePerm⁻¹ d₃ = d₂ := by rw [Perm.inv_eq_iff_eq]; exact f23.symm
  have i0 : M.facePerm⁻¹ d₀ = d₃ := by rw [Perm.inv_eq_iff_eq]; exact f30.symm
  refine ⟨f01, f12, f23, f30, fun e he => ?_, ne02, ne13⟩
  obtain ⟨i, rfl⟩ := he
  induction i using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [add_comm, zpow_add, zpow_one, Perm.mul_apply]
    rcases ih with h | h | h | h <;> rw [h] <;> simp [f01, f12, f23, f30]
  | pred i ih =>
    rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one, Perm.mul_apply]
    rcases ih with h | h | h | h <;> rw [h] <;> simp [i0, i1, i2, i3]

/-- **A 4-cycle with empty forward side and no chord is a four-face.** -/
theorem Cyc4.fourFace {a b c d : V} (h : Cyc4 G a b c d) (M : PlaneMap G)
    (nac : ¬ G.Adj a c) (nbd : ¬ G.Adj b d) (hno : ∀ w, ¬ In4 M a b c d w) :
    FourFace M ⟨(a, b), h.hab⟩ ⟨(b, c), h.hbc⟩ ⟨(c, d), h.hcd⟩ ⟨(d, a), h.hda⟩ := by
  have hno1 : ∀ w, ¬ In4 M b c d a w := by rw [← in4_rot]; exact hno
  have hno2 : ∀ w, ¬ In4 M c d a b w := by rw [← in4_rot]; exact hno1
  have hno3 : ∀ w, ¬ In4 M d a b c w := by rw [← in4_rot]; exact hno2
  refine fourFace_of_facePerm M ?_ ?_ ?_ ?_ h.ac h.bd
  · exact h.rot.rot_eq_of_empty M nbd hno1
  · exact h.rot.rot.rot_eq_of_empty M (fun h' => nac h'.symm) hno2
  · exact h.rot.rot.rot.rot_eq_of_empty M (fun h' => nbd h'.symm) hno3
  · exact h.rot_eq_of_empty M nac hno


/-! ### Case 3.2: auxiliary reductions -/

theorem c32_nbr (hG : GAMin G) (u : V) : ∃ w, G.Adj u w :=
  (G.degree_pos_iff_exists_adj u).1 (by have := hG.isCritical4.three_le_degree u; omega)

theorem c32_conn (hG : GAMin G) (u v : V) : RIn G Set.univ u v := by
  obtain ⟨u', hu⟩ := c32_nbr hG u
  obtain ⟨v', hv⟩ := c32_nbr hG v
  have := hG.rIn_of_clique (S := ∅) (by simp) (d := ⟨(u, u'), hu⟩) (e := ⟨(v, v'), hv⟩)
    (by simp) (by simp)
  simpa using this

/-- **Identifying a vertex `p` of degree three into `w` across a face.** If `N(p) = {q, z, r}`,
`w ~ z, r`, `p q z` is a triangle and `z` is the only common neighbour of `w` and `q`, then
identifying `p` into `w` gives a smaller planar graph with at most three triangles. -/
theorem c32_glue (hG : GAMin G) (M : PlaneMap G) (o : G.Dart)
    (hinj : ∀ e e' : FaceApex.F M o, e.1.fst = e'.1.fst → e = e') {p q z r w : V}
    (hw : w ∈ FaceApex.faceVerts M o) (hp : p ∈ FaceApex.faceVerts M o) (hwp : w ≠ p)
    (nwp : ¬ G.Adj w p) (hN : ∀ u, G.Adj p u → u = q ∨ u = z ∨ u = r)
    (hpq : G.Adj p q) (hpz : G.Adj p z) (hqz : G.Adj q z) (hwz : G.Adj w z) (hwr : G.Adj w r)
    (nqr : ¬ G.Adj q r) (hs : ∀ c, G.Adj w c → G.Adj q c → c = z) : False := by
  set emb : {v // v ≠ p} ↪ V := Function.Embedding.subtype _ with hemb
  have hwq : w ≠ q := fun h => nwp (h ▸ hpq.symm)
  have hwz' : w ≠ z := hwz.ne
  have hqz' : q ≠ z := hqz.ne
  -- the triangles of the identified graph
  have hclass : ∀ t : Finset {v // v ≠ p}, (glue G w p).IsNClique 3 t →
      ¬ G.IsNClique 3 (t.map emb) → t.map emb = {w, q, z} := by
    intro t ht hnot
    have hcard : (t.map emb).card = 3 := by rw [Finset.card_map]; exact ht.card_eq
    have hmem : ∀ u, u ∈ t.map emb ↔ ∃ h : u ≠ p, (⟨u, h⟩ : {v // v ≠ p}) ∈ t := by
      intro u
      simp only [Finset.mem_map, hemb, Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨x.2, hx⟩
      · rintro ⟨h, hx⟩; exact ⟨_, hx, rfl⟩
    have gadj : ∀ u ∈ t.map emb, ∀ u' ∈ t.map emb, u ≠ u' → ∃ (h1 : u ≠ p) (h2 : u' ≠ p),
        (glue G w p).Adj ⟨u, h1⟩ ⟨u', h2⟩ := by
      intro u hu u' hu' huu'
      obtain ⟨h1, h1'⟩ := (hmem u).1 hu
      obtain ⟨h2, h2'⟩ := (hmem u').1 hu'
      exact ⟨h1, h2, ht.1 h1' h2' fun e => huu' (congrArg Subtype.val e)⟩
    have plain : ∀ u ∈ t.map emb, ∀ u' ∈ t.map emb, u ≠ u' → u ≠ w → u' ≠ w → G.Adj u u' := by
      intro u hu u' hu' huu' h1 h2
      obtain ⟨_, _, h⟩ := gadj u hu u' hu' huu'
      exact c31_glue_adj_plain h1 h2 h
    have fromw : ∀ u ∈ t.map emb, u ≠ w → w ∈ t.map emb → G.Adj w u ∨ G.Adj p u := by
      intro u hu huw hw'
      obtain ⟨_, _, h⟩ := gadj w hw' u hu (Ne.symm huw)
      exact c31_glue_adj_fromx rfl huw h
    have hwt : w ∈ t.map emb := by
      by_contra hx
      exact hnot (c31_glue_tri_plain ht hx)
    obtain ⟨b, hb, hbw, nwb⟩ : ∃ b ∈ t.map emb, b ≠ w ∧ ¬ G.Adj w b := by
      by_contra hno
      push Not at hno
      refine hnot ⟨fun u hu u' hu' huu' => ?_, hcard⟩
      by_cases h1 : u = w
      · subst h1; exact hno u' hu' (Ne.symm huu')
      by_cases h2 : u' = w
      · subst h2; exact (hno u hu huu').symm
      exact plain u hu u' hu' huu' h1 h2
    have hbq : b = q := by
      rcases (fromw b hb hbw hwt).resolve_left nwb |> hN b with h | h | h
      · exact h
      · exact absurd (h ▸ hwz) nwb
      · exact absurd (h ▸ hwr) nwb
    subst hbq
    have hsub : t.map emb ⊆ {w, b, z} := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases h1 : u = w
      · exact Or.inl h1
      by_cases h2 : u = b
      · exact Or.inr (Or.inl h2)
      right; right
      have hbu : G.Adj b u := plain b hb u hu (Ne.symm h2) hbw h1
      rcases fromw u hu h1 hwt with h | h
      · exact hs u h hbu
      · rcases hN u h with h' | h' | h'
        · exact absurd h' h2
        · exact h'
        · exact absurd (h' ▸ hbu) nqr
    refine (Finset.eq_of_subset_of_card_le hsub ?_)
    rw [hcard]
    exact Finset.card_le_three
  have hT : G.IsNClique 3 ({p, q, z} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hpq, hpz, hqz⟩
  have hpt : ∀ t : Finset {v // v ≠ p}, p ∉ t.map emb := fun t h => by
    obtain ⟨x, -, hx⟩ := Finset.mem_map.mp h
    exact x.2 hx
  have htri : triCount (glue G w p) ≤ triCount G := by
    unfold triCount
    refine Nat.card_le_card_of_injective (fun t => if h : G.IsNClique 3 (t.1.map emb) then
      ⟨t.1.map emb, h⟩ else ⟨{p, q, z}, hT⟩) ?_
    rintro ⟨t, ht⟩ ⟨t', ht'⟩ heq
    apply Subtype.ext
    apply Finset.map_injective emb
    by_cases h1 : G.IsNClique 3 (t.map emb) <;> by_cases h2 : G.IsNClique 3 (t'.map emb) <;>
      simp only [h1, h2, ↓reduceDIte, Subtype.mk.injEq] at heq
    · exact heq
    · exact absurd (heq ▸ Finset.mem_insert_self p _) (hpt t)
    · exact absurd (heq.symm ▸ Finset.mem_insert_self p _) (hpt t')
    · rw [hclass t ht h1, hclass t' ht' h2]
  have hcol : (glue G w p).Colorable 3 := by
    refine hG.small {v // v ≠ p} (glue G w p) ?_ (isPlanar_glue M o hinj hwp hw hp)
      (htri.trans hG.tri)
    have h1 : Fintype.card {v // v ≠ p} < Fintype.card V :=
      Fintype.card_subtype_lt (p := (· ≠ p)) (x := p) (by simp)
    have h2 := card_edgeSet_glue_le (G := G) w p hwp
    omega
  exact hG.not_colorable (colorable_of_glue hwp nwp hcol)


omit [Fintype V] in
/-- Four darts at a vertex closed under the rotation contain all darts at that vertex. -/
theorem c32_nbr_of_rot4 (M : PlaneMap G) {w p₁ p₂ p₃ p₄ : V} (h₁ : G.Adj w p₁)
    (h₂ : G.Adj w p₂) (h₃ : G.Adj w p₃) (h₄ : G.Adj w p₄)
    (r12 : M.rot ⟨(w, p₁), h₁⟩ = ⟨(w, p₂), h₂⟩) (r23 : M.rot ⟨(w, p₂), h₂⟩ = ⟨(w, p₃), h₃⟩)
    (r34 : M.rot ⟨(w, p₃), h₃⟩ = ⟨(w, p₄), h₄⟩) (r41 : M.rot ⟨(w, p₄), h₄⟩ = ⟨(w, p₁), h₁⟩) :
    ∀ u, G.Adj w u → u = p₁ ∨ u = p₂ ∨ u = p₃ ∨ u = p₄ := by
  set d₁ : G.Dart := ⟨(w, p₁), h₁⟩
  set d₂ : G.Dart := ⟨(w, p₂), h₂⟩
  set d₃ : G.Dart := ⟨(w, p₃), h₃⟩
  set d₄ : G.Dart := ⟨(w, p₄), h₄⟩
  have i1 : M.rot⁻¹ d₁ = d₄ := by rw [Perm.inv_eq_iff_eq]; exact r41.symm
  have i2 : M.rot⁻¹ d₂ = d₁ := by rw [Perm.inv_eq_iff_eq]; exact r12.symm
  have i3 : M.rot⁻¹ d₃ = d₂ := by rw [Perm.inv_eq_iff_eq]; exact r23.symm
  have i4 : M.rot⁻¹ d₄ = d₃ := by rw [Perm.inv_eq_iff_eq]; exact r34.symm
  have hmem : ∀ i : ℤ, (M.rot ^ i) d₁ = d₁ ∨ (M.rot ^ i) d₁ = d₂ ∨ (M.rot ^ i) d₁ = d₃ ∨
      (M.rot ^ i) d₁ = d₄ := by
    intro i
    induction i using Int.induction_on with
    | zero => simp
    | succ i ih =>
      rw [add_comm, zpow_add, zpow_one, Perm.mul_apply]
      rcases ih with h | h | h | h <;> rw [h] <;> simp [r12, r23, r34, r41]
    | pred i ih =>
      rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one, Perm.mul_apply]
      rcases ih with h | h | h | h <;> rw [h] <;> simp [i1, i2, i3, i4]
  intro u hu
  obtain ⟨i, hi⟩ := M.isRotationSystem.sameCycle d₁ ⟨(w, u), hu⟩ rfl
  have hs := fun (d : G.Dart) (h : d = ⟨(w, u), hu⟩) => (congrArg (fun d : G.Dart => d.snd) h).symm
  rcases hmem i with h | h | h | h <;> rw [h] at hi
  · exact Or.inl (hs _ hi)
  · exact Or.inr (Or.inl (hs _ hi))
  · exact Or.inr (Or.inr (Or.inl (hs _ hi)))
  · exact Or.inr (Or.inr (Or.inr (hs _ hi)))

/-- **Step 1 of Case 3.2.** A vertex `w` of a smallest counterexample cannot lie on all of its
triangles while its rotation passes through `p₁ p₂ p₃ p₄` with triangles `w p₃ p₄`, `w p₄ p₁`
(it would have degree four and `G - w` would be triangle-free). -/
theorem c32_deg4 (hG : GAMin G) (M : PlaneMap G) {w p₁ p₂ p₃ p₄ : V}
    (h₁ : G.Adj w p₁) (h₂ : G.Adj w p₂) (h₃ : G.Adj w p₃) (h₄ : G.Adj w p₄)
    (d13 : p₁ ≠ p₃) (d24 : p₂ ≠ p₄) (d34 : p₃ ≠ p₄)
    (r12 : M.rot ⟨(w, p₁), h₁⟩ = ⟨(w, p₂), h₂⟩) (r23 : M.rot ⟨(w, p₂), h₂⟩ = ⟨(w, p₃), h₃⟩)
    (a34 : G.Adj p₃ p₄) (a41 : G.Adj p₄ p₁) {T : Finset V} (hT : G.IsNClique 3 T)
    (hwT : w ∈ T) (hT1 : T ≠ {w, p₃, p₄}) (hT2 : T ≠ {w, p₄, p₁}) : False := by
  have r34 : M.rot ⟨(w, p₃), h₃⟩ = ⟨(w, p₄), h₄⟩ := by
    rcases c31_tri_rot hG M h₄ a34.symm h₃ ⟨(w, p₃), h₃⟩ ⟨(w, p₄), h₄⟩ rfl rfl rfl rfl with h | h
    · exact h
    · exfalso
      have := M.rot.injective (h.trans r23.symm)
      exact d24 (congrArg (fun d : G.Dart => d.snd) this).symm
  have r41 : M.rot ⟨(w, p₄), h₄⟩ = ⟨(w, p₁), h₁⟩ := by
    rcases c31_tri_rot hG M h₁ a41.symm h₄ ⟨(w, p₄), h₄⟩ ⟨(w, p₁), h₁⟩ rfl rfl rfl rfl with h | h
    · exact h
    · exfalso
      have := h.symm.trans r12
      exact d24 (congrArg (fun d : G.Dart => d.snd) this).symm
  have hN := c32_nbr_of_rot4 M h₁ h₂ h₃ h₄ r12 r23 r34 r41
  have hw1 : w ≠ p₁ := h₁.ne
  have hw3 : w ≠ p₃ := h₃.ne
  have hw4 : w ≠ p₄ := h₄.ne
  have t1 : G.IsNClique 3 ({w, p₃, p₄} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨h₃, h₄, a34⟩
  have t2 : G.IsNClique 3 ({w, p₄, p₁} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨h₄, h₁, a41⟩
  have hall : ∀ T' : Finset V, G.IsNClique 3 T' → w ∈ T' := by
    intro T' hT'
    by_contra hw
    have := c31_four_le_triCount hT t1 t2 hT' hT1 hT2 (c31_ne_of_mem hwT hw)
      (c31_ne_of_mem (u := p₃) (by simp) (by simp [hw3.symm, d34, d13.symm]))
      (c31_ne_of_mem (u := w) (by simp) hw) (c31_ne_of_mem (u := w) (by simp) hw)
    have := hG.tri
    omega
  refine hG.not_colorable (colorable_of_induce_planar_cliqueFree G w ?_ ?_ ?_)
  · exact isPlanar_of_injective_hom' Subtype.val Subtype.val_injective (fun a b h => h) hG.planar
  · intro t ht
    let e : ({u | u ≠ w} : Set V) ↪ V := Function.Embedding.subtype _
    have hle : (G.induce {u | u ≠ w}).map e ≤ G := by
      intro u v h
      obtain ⟨a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj e _ u v).1 h
      exact hab
    have hw := hall _ ((ht.map).mono hle)
    obtain ⟨x, -, hx⟩ := Finset.mem_map.mp hw
    exact x.2 hx
  · rw [← SimpleGraph.card_neighborFinset_eq_degree]
    calc _ ≤ ({p₁, p₂, p₃, p₄} : Finset V).card := Finset.card_le_card fun u hu => by
          have := hN u ((SimpleGraph.mem_neighborFinset _ _ _).1 hu)
          simpa using this
      _ ≤ 4 := Finset.card_le_four

/-- One side of a separator with the extension property, as an explicit component, contains a
triangle. -/
theorem c32_tri_side (hG : GAMin G) {S : Set V} (hext : ExtProp G S) {w : V} (hw : w ∉ S) :
    ∃ t : Finset V, G.IsNClique 3 t ∧ ∀ u ∈ t, u ∈ S ∨ (u ∉ S ∧ RIn G Sᶜ w u) := by
  set K : Set V := {u | u ∉ S ∧ RIn G Sᶜ w u} with hK
  have hclose : ∀ a u, a ∈ K → G.Adj a u → u ∉ S → u ∈ K := fun a u ha hau hu =>
    ⟨hu, Relation.ReflTransGen.tail ha.2 ⟨hau, ha.1, hu⟩⟩
  have hcross : ∀ a b, G.Adj a b → (a ∈ S ∪ K ∧ b ∈ S ∪ K) ∨ (a ∈ Kᶜ ∧ b ∈ Kᶜ) := by
    intro a b hab
    by_cases ha : a ∈ K
    · left
      refine ⟨Or.inr ha, ?_⟩
      by_cases hb : b ∈ S
      · exact Or.inl hb
      · exact Or.inr (hclose a b ha hab hb)
    · by_cases hb : b ∈ K
      · left
        refine ⟨?_, Or.inr hb⟩
        by_contra haS
        rw [Set.mem_union, not_or] at haS
        exact ha (hclose b a hb hab.symm haS.1)
      · exact Or.inr ⟨ha, hb⟩
  obtain ⟨w', hw'⟩ := c32_nbr hG w
  have hB : Nat.card (restrict G Kᶜ).edgeSet < Nat.card G.edgeSet :=
    card_edgeSet_restrict_lt hw' fun h => h ⟨hw, RIn.refl _⟩
  have h3 := hG.not_cliqueFree_of_extProp hext (A := S ∪ K) (B := Kᶜ) Set.subset_union_left
    (fun s hs hsK => hsK.1 hs) (by
      rintro u (hu | hu) huK
      · exact hu
      · exact absurd hu huK) hcross hB
  simp only [SimpleGraph.CliqueFree, not_forall, not_not] at h3
  obtain ⟨t, ht⟩ := h3
  refine ⟨t, ht.mono (restrict_le G _), fun u hu => ?_⟩
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := SimpleGraph.is3Clique_iff.mp ht
  have hmem : u ∈ S ∪ K := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact hpq.2.1
    · exact hpq.2.2
    · exact hpr.2.2
  rcases hmem with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **A cut vertex argument.** Let `I` and `J` be unions of components of `G - A` and `G - B`
with `A ∩ B ⊆ {z}`. If `J` avoids `A \ {z}` and `I` avoids `B \ {z}`, then `I` and `J` are
disjoint (a path from a common vertex to `A ∪ B` avoiding `z` would leave both). -/
theorem c32_disj (hG : GAMin G) {A B : Set V} {z v : V} {I J : V → Prop}
    (hAB : ∀ q, q ∈ A → q ∈ B → q = z) (hzA : z ∈ A)
    (hIA : ∀ u, I u → u ∉ A) (hJB : ∀ u, J u → u ∉ B)
    (hIcl : ∀ u u', I u → G.Adj u u' → u' ∉ A → I u')
    (hJcl : ∀ u u', J u → G.Adj u u' → u' ∉ B → J u')
    (hAJ : ∀ q ∈ A, q ≠ z → ¬ J q) (hBI : ∀ q ∈ B, q ≠ z → ¬ I q)
    (hv : v ∈ A) (hvz : v ≠ z) {u : V} (hI : I u) (hJ : J u) : False := by
  have huz : u ≠ z := fun h => hIA u hI (h ▸ hzA)
  obtain ⟨u', hu'⟩ := c32_nbr hG u
  obtain ⟨v', hv'⟩ := c32_nbr hG v
  have hS : ∀ x ∈ ({z} : Set V), ∀ y ∈ ({z} : Set V), x ≠ y → G.Adj x y := by
    rintro x rfl y rfl h; exact absurd rfl h
  have hr := hG.rIn_of_clique hS (d := ⟨(u, u'), hu'⟩) (e := ⟨(v, v'), hv'⟩) huz hvz
  simp only at hr
  obtain ⟨p, q, hup, -, hp, hqz, hq, hpq⟩ :=
    hr.exit (P := (A ∪ B)ᶜ) (by simp [hIA u hI, hJB u hJ]) (by simp [hv])
  have key : ∀ x, RIn G ({z}ᶜ ∩ (A ∪ B)ᶜ) u x → I x ∧ J x := by
    intro x hx
    induction hx with
    | refl => exact ⟨hI, hJ⟩
    | @tail b c _ hst ih =>
      obtain ⟨hab, -, hb⟩ := hst
      have hb' : c ∉ A ∧ c ∉ B := by simpa using hb.2
      exact ⟨hIcl _ _ ih.1 hab hb'.1, hJcl _ _ ih.2 hab hb'.2⟩
  obtain ⟨hIp, hJp⟩ := key p hup
  have hq' : q ∈ A ∪ B := not_not.1 hq
  have hqz' : q ≠ z := hqz
  rcases hq' with hqA | hqB
  · have hqB : q ∉ B := fun h => hqz' (hAB q hqA h)
    exact hAJ q hqA hqz' (hJcl p q hJp hpq hqB)
  · have hqA : q ∉ A := fun h => hqz' (hAB q h hqB)
    exact hBI q hqB hqz' (hIcl p q hIp hpq hqA)


omit [Fintype V] in
/-- The graph induced on `A` plus the edge `z w`. -/
def c32H1 (G : SimpleGraph V) (A : Set V) (z w : V) : SimpleGraph A where
  Adj a b := a ≠ b ∧ (G.Adj a b ∨ (a.1 = z ∧ b.1 = w) ∨ (a.1 = w ∧ b.1 = z))
  symm := ⟨fun a b h => ⟨h.1.symm, by
    rcases h.2 with h' | h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr (Or.inr ⟨h'.2, h'.1⟩)
    · exact Or.inr (Or.inl ⟨h'.2, h'.1⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- **The final gluing of Case 3.2.** Suppose `V = A ∪ B` with `A ∩ B = {z}`, the only edges
between `A \ {z}` and `B \ {z}` are `v₀ v₁` and `v₃ v₂`, the only triangle inside `A` is `Ta`
and the only common neighbours of `z` and `v₃` in `A` are `v₀` and `x`. Then `G` is
3-colourable: colour `G[A] + z v₃` by minimality, colour `G[B]`, and match the colours. -/
theorem c32_endgame (hG : GAMin G) {v₀ v₁ v₂ v₃ z x y : V} {A B : Set V} {Ta : Finset V}
    (h0 : G.Adj v₀ z) (a30 : G.Adj v₃ v₀) (h1 : G.Adj v₁ z) (a12 : G.Adj v₁ v₂)
    (a23 : G.Adj v₂ v₃) (hzy : G.Adj z y) (hy2 : G.Adj y v₂) (hz3 : z ≠ v₃) (h2z : v₂ ≠ z)
    (hzA : z ∈ A) (h0A : v₀ ∈ A) (h3A : v₃ ∈ A) (hzB : z ∈ B) (h1B : v₁ ∈ B) (h2B : v₂ ∈ B)
    (hyB : y ∈ B) (hAB : ∀ u, u ∈ A → u ∈ B → u = z)
    (hcross : ∀ a b, G.Adj a b → (a ∈ A ∧ b ∈ A) ∨ (a ∈ B ∧ b ∈ B) ∨ (a = v₀ ∧ b = v₁) ∨
      (a = v₁ ∧ b = v₀) ∨ (a = v₃ ∧ b = v₂) ∨ (a = v₂ ∧ b = v₃))
    (hBlt : Nat.card (restrict G B).edgeSet < Nat.card G.edgeSet)
    (hTa : ∀ t : Finset V, G.IsNClique 3 t → (∀ u ∈ t, u ∈ A) → t = Ta)
    (hcommon : ∀ s ∈ A, G.Adj z s → G.Adj v₃ s → s = v₀ ∨ s = x) : False := by
  have hyA : y ∉ A := fun h => hzy.ne (hAB y h hyB).symm
  have h2A : v₂ ∉ A := fun h => h2z (hAB v₂ h h2B)
  have h1A : v₁ ∉ A := fun h => h1.ne (hAB v₁ h h1B)
  set H1 := c32H1 G A z v₃ with hH1
  -- planarity: contract `z y v₂`
  have hP : IsPlanar H1 := by
    let br : A → Finset V := fun a => if a.1 = z then {z, y, v₂} else {a.1}
    have hmem : ∀ a : A, a.1 ∈ br a := fun a => by
      by_cases ha : a.1 = z
      · simp [br, ha]
      · simp [br, ha]
    have hy' : ∀ b : A, b.1 ≠ y := fun b h => hyA (h ▸ b.2)
    have h2' : ∀ b : A, b.1 ≠ v₂ := fun b h => h2A (h ▸ b.2)
    refine isPlanar_of_minorModel hG.planar
      { branch := br
        branch_nonempty := fun a => ⟨_, hmem a⟩
        branch_connected := fun a => ?_
        branch_disjoint := fun a a' haa' => ?_
        branch_adjacent := fun a b hab => ?_ }
    · rw [← connSet_iff_induce_connected]
      by_cases ha : a.1 = z
      · have c1 : ConnSet G ({y, v₂} : Set V) :=
          (connSet_singleton G v₂).insert_adj (Set.mem_singleton _) hy2
        have c2 := c1.insert_adj (a := z) (Set.mem_insert _ _) hzy
        simpa [br, ha] using c2
      · simpa [br, ha] using connSet_singleton G a.1
    · rw [Finset.disjoint_left]
      intro u hu hu'
      have hne : a.1 ≠ a'.1 := fun h => haa' (Subtype.ext h)
      by_cases ha : a.1 = z <;> by_cases ha' : a'.1 = z
      · exact hne (ha.trans ha'.symm)
      · simp only [br, ha, ha', ite_true, ite_false, Finset.mem_insert,
          Finset.mem_singleton] at hu hu'
        subst hu'
        rcases hu with h | h | h
        · exact ha' h
        · exact hy' a' h
        · exact h2' a' h
      · simp only [br, ha, ha', ite_true, ite_false, Finset.mem_insert,
          Finset.mem_singleton] at hu hu'
        subst hu
        rcases hu' with h | h | h
        · exact ha h
        · exact hy' a h
        · exact h2' a h
      · simp only [br, ha, ha', ite_false, Finset.mem_singleton] at hu hu'
        exact hne (hu.symm.trans hu')
    · rcases hab.2 with h | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact ⟨_, hmem a, _, hmem b, h⟩
      · exact ⟨v₂, by simp [br, ha], b.1, hmem b, hb ▸ a23⟩
      · exact ⟨a.1, hmem a, v₂, by simp [br, hb], ha ▸ a23.symm⟩
  -- at most three triangles
  have htri : triCount H1 ≤ 3 := by
    set emb : A ↪ V := Function.Embedding.subtype _ with hemb
    set S3 : Finset (Finset V) := {Ta, {z, v₃, v₀}, {z, v₃, x}} with hS3
    have key : ∀ t : Finset A, H1.IsNClique 3 t → t.map emb ∈ S3 := by
      intro t ht
      have hcard : (t.map emb).card = 3 := by rw [Finset.card_map]; exact ht.card_eq
      have hA : ∀ u ∈ t.map emb, u ∈ A := fun u hu => by
        obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp hu; exact b.2
      have hadj : ∀ u ∈ t.map emb, ∀ u' ∈ t.map emb, u ≠ u' →
          G.Adj u u' ∨ (u = z ∧ u' = v₃) ∨ (u = v₃ ∧ u' = z) := by
        intro u hu u' hu' hne
        obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hu
        obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hu'
        exact (ht.1 hb hb' (fun e => hne (congrArg _ e))).2
      by_cases hG3 : G.IsNClique 3 (t.map emb)
      · rw [hTa _ hG3 hA]; simp [hS3]
      have hz : z ∈ t.map emb ∧ v₃ ∈ t.map emb := by
        by_contra hno
        apply hG3
        refine ⟨fun u hu u' hu' hne => ?_, hcard⟩
        rcases hadj u hu u' hu' hne with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h
        · exact absurd ⟨hu, hu'⟩ hno
        · exact absurd ⟨hu', hu⟩ hno
      have hsub : ∀ s ∈ t.map emb, s = z ∨ s = v₃ ∨ s = v₀ ∨ s = x := by
        intro s hs
        by_cases e1 : s = z
        · exact Or.inl e1
        by_cases e2 : s = v₃
        · exact Or.inr (Or.inl e2)
        have g1 : G.Adj z s := by
          rcases hadj z hz.1 s hs (Ne.symm e1) with h | h | h
          · exact h
          · exact absurd h.2 e2
          · exact absurd h.1 hz3
        have g2 : G.Adj v₃ s := by
          rcases hadj v₃ hz.2 s hs (Ne.symm e2) with h | h | h
          · exact h
          · exact absurd h.1 hz3.symm
          · exact absurd h.2 e1
        exact Or.inr (Or.inr (hcommon s (hA s hs) g1 g2))
      by_cases h0t : v₀ ∈ t.map emb
      · have hc3 : ({z, v₃, v₀} : Finset V).card = 3 :=
          Finset.card_eq_three.mpr ⟨z, v₃, v₀, hz3, h0.ne.symm, a30.ne, rfl⟩
        have : ({z, v₃, v₀} : Finset V) = t.map emb := by
          refine Finset.eq_of_subset_of_card_le (fun u hu => ?_) (by rw [hcard, hc3])
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl
          · exact hz.1
          · exact hz.2
          · exact h0t
        rw [← this]; simp [hS3]
      · have : t.map emb = {z, v₃, x} := by
          refine Finset.eq_of_subset_of_card_le (fun u hu => ?_) (by rw [hcard]; exact Finset.card_le_three)
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hsub u hu with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact absurd (h ▸ hu) h0t
          · exact Or.inr (Or.inr h)
        rw [this]; simp [hS3]
    unfold triCount
    calc Nat.card {t // H1.IsNClique 3 t} ≤ Nat.card {s // s ∈ S3} :=
          Nat.card_le_card_of_injective (fun t => ⟨t.1.map emb, key t.1 t.2⟩)
            (fun t t' h => Subtype.ext (Finset.map_injective emb (congrArg Subtype.val h)))
      _ = S3.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ ≤ 3 := Finset.card_le_three
  -- fewer vertices, no more edges
  have hsize : Fintype.card A + Nat.card H1.edgeSet < Fintype.card V + Nat.card G.edgeSet := by
    have hV : Fintype.card A < Fintype.card V := by
      have := Fintype.card_subtype_lt (p := fun v => v ∈ A) (x := y) hyA
      convert this
    have hE : Nat.card H1.edgeSet ≤ Nat.card G.edgeSet := by
      have hnot : ∀ e ∈ H1.edgeSet, Sym2.map Subtype.val e ∉ G.edgeSet →
          Sym2.map Subtype.val e = s(z, v₃) := by
        intro e he hn
        induction e using Sym2.ind with
        | _ a b =>
          rcases he.2 with h | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact absurd h hn
          · rw [Sym2.map_mk, ha, hb]
          · rw [Sym2.map_mk, ha, hb, Sym2.eq_swap]
      have hy : ∀ e : Sym2 A, Sym2.map Subtype.val e ≠ s(y, v₂) := by
        intro e he
        have : y ∈ Sym2.map Subtype.val e := by rw [he]; exact Sym2.mem_mk_left _ _
        obtain ⟨b, -, hb⟩ := Sym2.mem_map.mp this
        exact hyA (hb ▸ b.2)
      refine Nat.card_le_card_of_injective (fun e => if h : Sym2.map Subtype.val e.1 ∈ G.edgeSet
        then ⟨_, h⟩ else ⟨s(y, v₂), hy2⟩) ?_
      rintro ⟨e, he⟩ ⟨e', he'⟩ heq
      apply Subtype.ext
      apply Sym2.map.injective Subtype.val_injective
      by_cases h1 : Sym2.map Subtype.val e ∈ G.edgeSet <;>
        by_cases h2 : Sym2.map Subtype.val e' ∈ G.edgeSet <;>
        simp only [h1, h2, ↓reduceDIte, Subtype.mk.injEq] at heq
      · exact heq
      · exact absurd (congrArg Subtype.val heq) (hy e)
      · exact absurd (congrArg Subtype.val heq).symm (hy e')
      · rw [hnot e he h1, hnot e' he' h2]
    omega
  obtain ⟨φ₁⟩ := hG.small A H1 hsize hP htri
  obtain ⟨φ₂⟩ := hG.colorable_restrict hBlt
  let zA : A := ⟨z, hzA⟩
  let v0A : A := ⟨v₀, h0A⟩
  let v3A : A := ⟨v₃, h3A⟩
  have c1 : φ₁ zA ≠ φ₁ v3A :=
    φ₁.valid ⟨fun e => hz3 (congrArg Subtype.val e), Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  have c2 : φ₁ v0A ≠ φ₁ v3A :=
    φ₁.valid ⟨fun e => a30.ne (congrArg Subtype.val e).symm, Or.inl a30.symm⟩
  have c3 : φ₂ z ≠ φ₂ v₁ := φ₂.valid ⟨h1.symm, hzB, h1B⟩
  have c4 : φ₂ v₁ ≠ φ₂ v₂ := φ₂.valid ⟨a12, h1B, h2B⟩
  obtain ⟨π, hπ⟩ := exists_perm_of_pattern (fun b : Bool => if b then φ₂ z else φ₂ v₁)
    (fun b : Bool => if b then φ₁ zA else φ₁ v3A) (by
      intro i j
      cases i <;> cases j <;> simp [c1, c3, Ne.symm c1, Ne.symm c3])
  have hπz : π (φ₂ z) = φ₁ zA := hπ true
  have hπ1 : π (φ₂ v₁) = φ₁ v3A := hπ false
  let C : V → Fin 3 := fun v => if h : v ∈ A then φ₁ ⟨v, h⟩ else π (φ₂ v)
  have hCA : ∀ v (h : v ∈ A), C v = φ₁ ⟨v, h⟩ := fun v h => by simp [C, h]
  have hCB : ∀ v ∈ B, C v = π (φ₂ v) := by
    intro v hv
    by_cases h : v ∈ A
    · obtain rfl := hAB v h hv
      rw [hCA v h, hπz]
    · simp [C, h]
  refine hG.not_colorable ⟨SimpleGraph.Coloring.mk C fun {a b} hab => ?_⟩
  rcases hcross a b hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  · rw [hCA a ha, hCA b hb]
    exact φ₁.valid ⟨fun e => hab.ne (congrArg Subtype.val e), Or.inl hab⟩
  · rw [hCB a ha, hCB b hb]
    exact π.injective.ne (φ₂.valid ⟨hab, ha, hb⟩)
  · rw [hCA _ h0A, hCB _ h1B, hπ1]; exact c2
  · rw [hCA _ h0A, hCB _ h1B, hπ1]; exact c2.symm
  · rw [hCA _ h3A, hCB _ h2B, ← hπ1]; exact π.injective.ne c4
  · rw [hCA _ h3A, hCB _ h2B, ← hπ1]; exact π.injective.ne c4.symm

/-- A 4-cycle has the extension property. -/
theorem Cyc4.extProp {a b c d : V} (h : Cyc4 G a b c d) : ExtProp G ({a, b, c, d} : Set V) := by
  have hinj : Function.Injective (fun i : ZMod 4 => (![a, b, c, d] : Fin 4 → V) i) := by
    intro i j hij
    have := h.ab; have := h.ac; have := h.ad; have := h.bc; have := h.bd; have := h.cd
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp at hij; simp_all)
  have hadj : ∀ i : ZMod 4, G.Adj ((fun i : ZMod 4 => (![a, b, c, d] : Fin 4 → V) i) i)
      ((fun i : ZMod 4 => (![a, b, c, d] : Fin 4 → V) i) (i + 1)) := by
    intro i
    fin_cases i
    · exact h.hab
    · exact h.hbc
    · exact h.hcd
    · exact h.hda
  have := extProp_four hinj hadj
  have he : Set.range (fun i : ZMod 4 => (![a, b, c, d] : Fin 4 → V) i) = {a, b, c, d} := by
    ext u; rw [c31_mem_range_four]; simp
  rwa [he] at this

/-- A 5-cycle has the extension property. -/
theorem c32_extProp_five {a b c d e : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hea : G.Adj e a) : ExtProp G ({a, b, c, d, e} : Set V) := by
  have hadj : ∀ i : ZMod 5, G.Adj ((fun i : ZMod 5 => (![a, b, c, d, e] : Fin 5 → V) i) i)
      ((fun i : ZMod 5 => (![a, b, c, d, e] : Fin 5 → V) i) (i + 1)) := by
    intro i
    fin_cases i
    · exact hab
    · exact hbc
    · exact hcd
    · exact hde
    · exact hea
  have := extProp_five hadj
  have he : Set.range (fun i : ZMod 5 => (![a, b, c, d, e] : Fin 5 → V) i) = {a, b, c, d, e} := by
    ext u
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
  rwa [he] at this

/-- From `p`, the darts `q, r, t` come in this order; then from `q`, `r` comes before `t`. -/
theorem rBefore_shift (M : PlaneMap G) {p q r t : G.Dart} (hq : p.fst = q.fst)
    (hr : p.fst = r.fst) (ht : p.fst = t.fst) (hqr : q ≠ r) (hrt : r ≠ t)
    (hqt : q ≠ t) (h1 : RBefore M p q r) (h2 : RBefore M p r t) : RBefore M q r t := by
  have h3 := rBefore_trans M hq hr ht hqr hrt hqt h1 h2
  rw [rBefore_iff M hq hr hqr] at h1
  rw [rBefore_iff M hr ht hrt] at h2
  rw [rBefore_iff M (hq.symm.trans hr) (hq.symm.trans ht) hrt]
  rw [rpos_sub M hq hr h1.le, rpos_sub M hq ht (h1.trans h2).le]
  omega

/-- If the rotation takes `a` to `b` and `b` to `c`, then from any other dart `a` comes before
`c`. -/
theorem rBefore_consec (M : PlaneMap G) {a b c d : G.Dart} (h1 : M.rot a = b) (h2 : M.rot b = c)
    (ha : d.fst = a.fst) (hdb : d ≠ b) (hdc : d ≠ c) (hac : a ≠ c) : RBefore M d a c := by
  have hb : a.fst = b.fst := by rw [← h1, M.isRotationSystem.fst_apply]
  have hc : b.fst = c.fst := by rw [← h2, M.isRotationSystem.fst_apply]
  have hdc' : d.fst = c.fst := ha.trans (hb.trans hc)
  have hdb' : d.fst = b.fst := ha.trans hb
  rw [rBefore_iff M ha hdc' hac]
  have pc := rpos_pos M hdc' (Ne.symm hdc)
  have pb := rpos_pos M hdb' (Ne.symm hdb)
  have sb : (M.rot ^ (rpos M d c - 1)) d = b := by
    apply M.rot.injective
    rw [← Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel pc, rpos_spec M hdc', h2]
  have lb := rpos_le M sb
  have sa : (M.rot ^ (rpos M d b - 1)) d = a := by
    apply M.rot.injective
    rw [← Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel pb, rpos_spec M hdb', h1]
  have la := rpos_le M sa
  omega

/-- If no neighbour of `a` lies on the forward side of the 4-cycle `a b c d`, the rotation at `a`
takes `a d` to `a b`. -/
theorem Cyc4.rot_eq_of_noadj {a b c d : V} (h : Cyc4 G a b c d) (M : PlaneMap G)
    (nac : ¬ G.Adj a c) (hno : ∀ w, G.Adj a w → ¬ In4 M a b c d w) :
    M.rot ⟨(a, d), h.hda.symm⟩ = ⟨(a, b), h.hab⟩ := by
  refine rot_eq_of_nextIn M (P := Cy4 a b c d) rfl (fun he => h.bd.symm
    (congrArg (fun g : G.Dart => g.snd) he)) ((h.dart_at rfl).2 (Or.inl rfl))
    (fun g hg hP => ((h.dart_at hg).1 hP).symm) (fun e f he hPe hf => ?_)
  have hfa : f.fst = a := (nextIn_fst M hf).trans he
  have hPf : Cy4 a b c d f := by obtain ⟨_, _, h', _⟩ := hf; exact h'
  rcases (h.dart_at hfa).1 hPf with rfl | rfl
  · exfalso
    have hadj := e.adj
    rw [he] at hadj
    have he' : e.snd ∉ ({a, b, c, d} : Set V) := by
      intro hm
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with h1 | h1 | h1 | h1
      · exact hadj.ne h1.symm
      · exact hPe ((h.dart_at he).2 (Or.inl (dart_eq_of he h1)))
      · exact nac (h1 ▸ hadj)
      · exact hPe ((h.dart_at he).2 (Or.inr (dart_eq_of he h1)))
    exact hno _ hadj ⟨he', e, _, by rw [he]; simp, he', hf, (h.fw_at rfl).2 rfl, RIn.refl _⟩
  · rfl

omit [Fintype V] in
/-- Two darts at a vertex swapped by the rotation contain all darts at that vertex. -/
theorem c32_nbr_of_rot2 (M : PlaneMap G) {w p₁ p₂ : V} (h₁ : G.Adj w p₁) (h₂ : G.Adj w p₂)
    (r12 : M.rot ⟨(w, p₁), h₁⟩ = ⟨(w, p₂), h₂⟩) (r21 : M.rot ⟨(w, p₂), h₂⟩ = ⟨(w, p₁), h₁⟩) :
    ∀ u, G.Adj w u → u = p₁ ∨ u = p₂ := by
  set d₁ : G.Dart := ⟨(w, p₁), h₁⟩
  set d₂ : G.Dart := ⟨(w, p₂), h₂⟩
  have i1 : M.rot⁻¹ d₁ = d₂ := by rw [Perm.inv_eq_iff_eq]; exact r21.symm
  have i2 : M.rot⁻¹ d₂ = d₁ := by rw [Perm.inv_eq_iff_eq]; exact r12.symm
  have hmem : ∀ i : ℤ, (M.rot ^ i) d₁ = d₁ ∨ (M.rot ^ i) d₁ = d₂ := by
    intro i
    induction i using Int.induction_on with
    | zero => simp
    | succ i ih =>
      rw [add_comm, zpow_add, zpow_one, Perm.mul_apply]
      rcases ih with h | h <;> rw [h] <;> simp [r12, r21]
    | pred i ih =>
      rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one, Perm.mul_apply]
      rcases ih with h | h <;> rw [h] <;> simp [i1, i2]
  intro u hu
  obtain ⟨i, hi⟩ := M.isRotationSystem.sameCycle d₁ ⟨(w, u), hu⟩ rfl
  have hs := fun (d : G.Dart) (h : d = ⟨(w, u), hu⟩) => (congrArg (fun d : G.Dart => d.snd) h).symm
  rcases hmem i with h | h <;> rw [h] at hi
  · exact Or.inl (hs _ hi)
  · exact Or.inr (hs _ hi)

/-- With three distinct triangles and at most three triangles, every triangle is one of them. -/
theorem c32_three_tri {T₁ T₂ T₃ : Finset V} (ht : triCount G ≤ 3) (h₁ : G.IsNClique 3 T₁)
    (h₂ : G.IsNClique 3 T₂) (h₃ : G.IsNClique 3 T₃) (h12 : T₁ ≠ T₂) (h13 : T₁ ≠ T₃)
    (h23 : T₂ ≠ T₃) {t : Finset V} (h : G.IsNClique 3 t) : t = T₁ ∨ t = T₂ ∨ t = T₃ := by
  by_contra hne
  push Not at hne
  have := c31_four_le_triCount h₁ h₂ h₃ h h12 h13 (Ne.symm hne.1) h23 (Ne.symm hne.2.1)
    (Ne.symm hne.2.2)
  omega

omit [Fintype V] in
theorem c32_dne {a p q : V} (hpq : p ≠ q) (h : G.Adj a p) (h' : G.Adj a q) :
    (⟨(a, p), h⟩ : G.Dart) ≠ ⟨(a, q), h'⟩ :=
  fun e => hpq (congrArg (fun d : G.Dart => d.snd) e)

/-- The configuration of Case 3.2 with the facts established in its first steps. -/
structure C32 (G : SimpleGraph V) (M : PlaneMap G) (v₀ v₁ v₂ v₃ z y x : V) : Prop where
  hG : GAMin G
  a01 : G.Adj v₀ v₁
  a12 : G.Adj v₁ v₂
  a23 : G.Adj v₂ v₃
  a30 : G.Adj v₃ v₀
  hF : FourFace M ⟨(v₀, v₁), a01⟩ ⟨(v₁, v₂), a12⟩ ⟨(v₂, v₃), a23⟩ ⟨(v₃, v₀), a30⟩
  n02 : ¬ G.Adj v₀ v₂
  n13 : ¬ G.Adj v₁ v₃
  h0 : G.Adj v₀ z
  h1 : G.Adj v₁ z
  hzy : G.Adj z y
  hy2 : G.Adj y v₂
  hzx : G.Adj z x
  hx3 : G.Adj x v₃
  n2 : ¬ G.Adj z v₂
  n3 : ¬ G.Adj z v₃
  ny0 : ¬ G.Adj y v₀
  nx1 : ¬ G.Adj x v₁
  hxy : x ≠ y
  nx0 : ¬ G.Adj x v₀
  ny1 : ¬ G.Adj y v₁
  nx2 : ¬ G.Adj x v₂
  ny3 : ¬ G.Adj y v₃
  r03 : M.rot ⟨(v₀, v₃), a30.symm⟩ = ⟨(v₀, v₁), a01⟩
  r01 : M.rot ⟨(v₀, v₁), a01⟩ = ⟨(v₀, z), h0⟩
  r1z : M.rot ⟨(v₁, z), h1⟩ = ⟨(v₁, v₀), a01.symm⟩
  r10 : M.rot ⟨(v₁, v₀), a01.symm⟩ = ⟨(v₁, v₂), a12⟩

namespace C32

variable {M : PlaneMap G} {v₀ v₁ v₂ v₃ z y x : V}

theorem z0 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : z ≠ v₀ := c.h0.ne.symm
theorem z1 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : z ≠ v₁ := c.h1.ne.symm
theorem z2 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : z ≠ v₂ := fun h => c.n02 (h ▸ c.h0)
theorem z3 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : z ≠ v₃ := fun h => c.n13 (h ▸ c.h1)
theorem x0 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : x ≠ v₀ := fun h => c.nx1 (h ▸ c.a01)
theorem x1 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : x ≠ v₁ := fun h => c.n13 (h ▸ c.hx3)
theorem x2 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : x ≠ v₂ := fun h => c.n2 (h ▸ c.hzx)
theorem x3 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : x ≠ v₃ := c.hx3.ne
theorem xz (c : C32 G M v₀ v₁ v₂ v₃ z y x) : x ≠ z := c.hzx.ne.symm
theorem y0 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : y ≠ v₀ := fun h => c.n02 (h ▸ c.hy2)
theorem y1 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : y ≠ v₁ := fun h => c.ny0 (h ▸ c.a01.symm)
theorem y2 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : y ≠ v₂ := c.hy2.ne
theorem y3 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : y ≠ v₃ := fun h => c.n3 (h ▸ c.hzy)
theorem yz (c : C32 G M v₀ v₁ v₂ v₃ z y x) : y ≠ z := c.hzy.ne.symm
theorem d02 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : v₀ ≠ v₂ := fun h => c.n2 (h ▸ c.h0.symm)
theorem d13 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : v₁ ≠ v₃ := fun h => c.n3 (h ▸ c.h1.symm)

theorem cyc1 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : Cyc4 G z v₀ v₃ x :=
  ⟨c.z0, c.z3, c.xz.symm, c.a30.ne.symm, c.x0.symm, c.x3.symm, c.h0.symm, c.a30.symm,
    c.hx3.symm, c.hzx.symm⟩

theorem cyc2 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : Cyc4 G z y v₂ v₁ :=
  ⟨c.yz.symm, c.z2, c.z1, c.y2, c.y1, c.a12.ne.symm, c.hzy, c.hy2, c.a12.symm, c.h1⟩

end C32

omit [Fintype V] in
theorem c32_nmem4 {a b c d w : V} (h1 : w ≠ a) (h2 : w ≠ b) (h3 : w ≠ c) (h4 : w ≠ d) :
    w ∉ ({a, b, c, d} : Set V) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨h1, h2, h3, h4⟩

namespace C32

variable {M : PlaneMap G} {v₀ v₁ v₂ v₃ z y x : V}

theorem v1_out1 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : In4 M x v₃ v₀ z v₁ := by
  have hC : Cyc4 G v₀ z x v₃ := c.cyc1.rev.rot.rot
  rw [in4_rot, in4_rot]
  exact hC.in4_of_rBefore M (e := ⟨(v₀, v₁), c.a01⟩) rfl
    (c32_nmem4 c.a01.ne.symm c.z1.symm c.x1.symm c.d13)
    (rBefore_of_rot M c.r01 (c32_dne c.z1.symm _ _) (c32_dne c.d13 _ _))

theorem v2_out1 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : In4 M x v₃ v₀ z v₂ :=
  in4_of_adj c.v1_out1 c.a12 (c32_nmem4 c.x2.symm c.a23.ne c.d02.symm c.z2.symm)

theorem y_out1 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : In4 M x v₃ v₀ z y :=
  in4_of_adj c.v2_out1 c.hy2.symm (c32_nmem4 c.hxy.symm c.y3 c.y0 c.yz)

theorem v0_out2 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : In4 M v₁ v₂ y z v₀ :=
  c.cyc2.rev.in4_of_rBefore M (e := ⟨(v₁, v₀), c.a01.symm⟩) rfl
    (c32_nmem4 c.a01.ne c.d02 c.y0.symm c.z0.symm)
    (rBefore_of_rot M c.r10 (c32_dne c.d02 _ _) (c32_dne c.z0.symm _ _))

theorem v3_out2 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : In4 M v₁ v₂ y z v₃ :=
  in4_of_adj c.v0_out2 c.a30.symm (c32_nmem4 c.d13.symm c.a23.ne.symm c.y3.symm c.z3.symm)

theorem x_out2 (c : C32 G M v₀ v₁ v₂ v₃ z y x) : In4 M v₁ v₂ y z x :=
  in4_of_adj c.v3_out2 c.hx3.symm (c32_nmem4 c.x1 c.x2 c.hxy c.xz)

theorem nbr0 (c : C32 G M v₀ v₁ v₂ v₃ z y x) {w : V} (hw : G.Adj v₀ w)
    (ho : In4 M x v₃ v₀ z w) : w = v₁ := by
  by_contra hne
  have hC : Cyc4 G v₀ z x v₃ := c.cyc1.rev.rot.rot
  rw [in4_rot, in4_rot] at ho
  have h1 := hC.rBefore_of_in4 M ho hw
  have hwm := in4_not_mem ho
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hwm
  have h2 := rBefore_consec M c.r03 c.r01 (d := ⟨(v₀, w), hw⟩) rfl (c32_dne hne _ _)
    (c32_dne hwm.2.1 _ _) (c32_dne c.z3.symm _ _)
  refine rBefore_asymm M ?_ ?_ ?_ h1 h2
  · rfl
  · rfl
  · exact c32_dne c.z3 _ _

theorem nbr1 (c : C32 G M v₀ v₁ v₂ v₃ z y x) {w : V} (hw : G.Adj v₁ w)
    (ho : In4 M v₁ v₂ y z w) : w = v₀ := by
  by_contra hne
  have h1 := c.cyc2.rev.rBefore_of_in4 M ho hw
  have hwm := in4_not_mem ho
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hwm
  have h2 := rBefore_consec M c.r1z c.r10 (d := ⟨(v₁, w), hw⟩) rfl (c32_dne hne _ _)
    (c32_dne hwm.2.1 _ _) (c32_dne c.z2 _ _)
  refine rBefore_asymm M ?_ ?_ ?_ h1 h2
  · rfl
  · rfl
  · exact c32_dne c.z2.symm _ _

theorem in1_ne (c : C32 G M v₀ v₁ v₂ v₃ z y x) : ∃ w, In4 M z v₀ v₃ x w := by
  by_contra hno
  push Not at hno
  have hF1 := c.cyc1.fourFace M c.n3 (fun h => c.nx0 h.symm) hno
  obtain ⟨-, m1, -, m3⟩ := hF1.mem_faceVerts
  have hN : ∀ u, G.Adj v₀ u → u = v₁ ∨ u = z ∨ u = v₃ :=
    c31_nbr_of_rot M c.d13 c.z3 ⟨(v₀, v₁), c.a01⟩ ⟨(v₀, z), c.h0⟩ ⟨(v₀, v₃), c.a30.symm⟩
      rfl rfl rfl rfl rfl rfl c.r01 (Or.inl hF1.f01) (Or.inl c.r03)
  refine c32_glue c.hG M _ hF1.inj m3 m1 c.x0 c.nx0 hN c.a01 c.h0 c.h1 c.hzx.symm c.hx3 c.n13 ?_
  intro t hxt h1t
  by_contra htz
  obtain ⟨n0, n1, n2, n3⟩ := c.hF.mem_faceVerts
  exact no_crossing_paths_of_ne M _ c.hF.inj c.a01 c.a12 c.a23 c.a30 c.d02 c.d13 n0 n1 n2 n3
    c.h0 c.hzy c.hy2 h1t hxt.symm c.hx3 ⟨c.z0, c.z1, c.z2, c.z3⟩ ⟨c.y0, c.y1, c.y2, c.y3⟩
    ⟨fun h => c.nx0 (h ▸ hxt), h1t.ne.symm, fun h => c.nx2 (h ▸ hxt),
      fun h => c.n13 (h ▸ h1t)⟩ ⟨c.x0, c.x1, c.x2, c.x3⟩ (Ne.symm htz) c.xz.symm
    (fun h => c.ny1 (h ▸ h1t.symm)) c.hxy.symm

theorem in2_ne (c : C32 G M v₀ v₁ v₂ v₃ z y x) : ∃ w, In4 M z y v₂ v₁ w := by
  by_contra hno
  push Not at hno
  have hF2 := c.cyc2.fourFace M c.n2 c.ny1 hno
  obtain ⟨-, m1, -, m3⟩ := hF2.mem_faceVerts
  have hN' : ∀ u, G.Adj v₁ u → u = z ∨ u = v₀ ∨ u = v₂ :=
    c31_nbr_of_rot M c.z2 c.d02 ⟨(v₁, z), c.h1⟩ ⟨(v₁, v₀), c.a01.symm⟩ ⟨(v₁, v₂), c.a12⟩
      rfl rfl rfl rfl rfl rfl c.r1z (Or.inl c.r10) (Or.inl hF2.f23)
  have hN : ∀ u, G.Adj v₁ u → u = v₀ ∨ u = z ∨ u = v₂ := fun u hu => by
    rcases hN' u hu with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  refine c32_glue c.hG M _ hF2.inj m1 m3 c.y1 c.ny1 hN c.a01.symm c.h1 c.h0 c.hzy.symm c.hy2
    c.n02 ?_
  intro t hyt h0t
  by_contra htz
  obtain ⟨n0, n1, n2, n3⟩ := c.hF.mem_faceVerts
  exact no_crossing_paths_of_ne M _ c.hF.inj c.a01 c.a12 c.a23 c.a30 c.d02 c.d13 n0 n1 n2 n3
    h0t hyt.symm c.hy2 c.h1 c.hzx c.hx3
    ⟨h0t.ne.symm, fun h => c.ny1 (h ▸ hyt), fun h => c.n02 (h ▸ h0t),
      fun h => c.ny3 (h ▸ hyt)⟩ ⟨c.y0, c.y1, c.y2, c.y3⟩ ⟨c.z0, c.z1, c.z2, c.z3⟩
    ⟨c.x0, c.x1, c.x2, c.x3⟩ htz (fun h => c.nx0 (h ▸ h0t.symm)) c.yz c.hxy.symm

end C32

/-- A 4-cycle together with its forward side. -/
def c32Cl (M : PlaneMap G) (a b c d : V) : Set V :=
  {u | u ∈ ({a, b, c, d} : Set V) ∨ In4 M a b c d u}

omit [Fintype V] in
/-- A triangle inside a three-element set contains all of it. -/
theorem c32_adj_of_sub3 {t : Finset V} {a b c : V} (ht : G.IsNClique 3 t)
    (hsub : ∀ u ∈ t, u = a ∨ u = b ∨ u = c) (hab : a ≠ b) : G.Adj a b := by
  have heq : t = {a, b, c} := Finset.eq_of_subset_of_card_le (fun u hu => by simpa using hsub u hu)
    (by rw [ht.card_eq]; exact Finset.card_le_three)
  exact ht.1 (by rw [heq]; simp) (by rw [heq]; simp) hab

namespace C32

variable {M : PlaneMap G} {v₀ v₁ v₂ v₃ z y x : V}

theorem s12 (c : C32 G M v₀ v₁ v₂ v₃ z y x) {q : V} (h1 : q ∈ ({z, v₀, v₃, x} : Set V))
    (h2 : q ∈ ({z, y, v₂, v₁} : Set V)) : q = z := by
  have := c.y0; have := c.y3; have := c.hxy; have := c.x1; have := c.x2; have := c.d02
  have := c.a23.ne; have := c.d13; have := c.a01.ne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
  rcases h1 with rfl | rfl | rfl | rfl <;> rcases h2 with h | h | h | h <;>
    first | rfl | exact h | exact absurd h ‹_› | exact absurd h.symm ‹_›

theorem not_in2_of_s1 (c : C32 G M v₀ v₁ v₂ v₃ z y x) {q : V}
    (h1 : q ∈ ({z, v₀, v₃, x} : Set V)) (hz : q ≠ z) : ¬ In4 M z y v₂ v₁ q := by
  intro h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  rcases h1 with rfl | rfl | rfl | rfl
  · exact hz rfl
  · exact c.cyc2.in4_disj M h c.v0_out2
  · exact c.cyc2.in4_disj M h c.v3_out2
  · exact c.cyc2.in4_disj M h c.x_out2

theorem not_in1_of_s2 (c : C32 G M v₀ v₁ v₂ v₃ z y x) {q : V}
    (h1 : q ∈ ({z, y, v₂, v₁} : Set V)) (hz : q ≠ z) : ¬ In4 M z v₀ v₃ x q := by
  intro h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  rcases h1 with rfl | rfl | rfl | rfl
  · exact hz rfl
  · exact c.cyc1.in4_disj M h c.y_out1
  · exact c.cyc1.in4_disj M h c.v2_out1
  · exact c.cyc1.in4_disj M h c.v1_out1

theorem disj (c : C32 G M v₀ v₁ v₂ v₃ z y x) {u : V} (hA : u ∈ c32Cl M z v₀ v₃ x)
    (hB : u ∈ c32Cl M z y v₂ v₁) : u = z := by
  by_contra hz
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact hz (c.s12 hA hB)
  · exact c.not_in2_of_s1 hA hz hB
  · exact c.not_in1_of_s2 hB hz hA
  · exact c32_disj c.hG (A := ({z, v₀, v₃, x} : Set V)) (B := ({z, y, v₂, v₁} : Set V))
      (fun q h1 h2 => c.s12 h1 h2) (by simp) (fun u h => in4_not_mem h)
      (fun u h => in4_not_mem h) (fun u u' h ha hn => in4_of_adj h ha hn)
      (fun u u' h ha hn => in4_of_adj h ha hn) (fun q h1 h2 => c.not_in2_of_s1 h1 h2)
      (fun q h1 h2 => c.not_in1_of_s2 h1 h2) (v := v₀) (by simp) c.z0.symm hA hB

theorem out1_of (c : C32 G M v₀ v₁ v₂ v₃ z y x) {u : V} (hu : u ∉ c32Cl M z v₀ v₃ x) :
    In4 M x v₃ v₀ z u := by
  simp only [c32Cl, Set.mem_ofPred_eq, not_or] at hu
  rcases c.cyc1.in4_total M hu.1 (s := z) (by simp) (c32_conn c.hG u z) with h | h
  · exact absurd h hu.2
  · exact h

theorem out2_of (c : C32 G M v₀ v₁ v₂ v₃ z y x) {u : V} (hu : u ∉ c32Cl M z y v₂ v₁) :
    In4 M v₁ v₂ y z u := by
  simp only [c32Cl, Set.mem_ofPred_eq, not_or] at hu
  rcases c.cyc2.in4_total M hu.1 (s := z) (by simp) (c32_conn c.hG u z) with h | h
  · exact absurd h hu.2
  · exact h

theorem v1_nA (c : C32 G M v₀ v₁ v₂ v₃ z y x) : v₁ ∉ c32Cl M z v₀ v₃ x := by
  rintro (h | h)
  · exact c.z1.symm (c.s12 h (by simp))
  · exact c.cyc1.in4_disj M h c.v1_out1

theorem v0_nB (c : C32 G M v₀ v₁ v₂ v₃ z y x) : v₀ ∉ c32Cl M z y v₂ v₁ := by
  rintro (h | h)
  · exact c.z0.symm (c.s12 (by simp) h)
  · exact c.cyc2.in4_disj M h c.v0_out2

end C32

omit [Fintype V] in
theorem cl_of_rIn {M : PlaneMap G} {a b c d w u : V} (hw : In4 M a b c d w)
    (hu : u ∈ ({a, b, c, d} : Set V) ∨ (u ∉ ({a, b, c, d} : Set V) ∧
      RIn G ({a, b, c, d} : Set V)ᶜ w u)) : u ∈ c32Cl M a b c d := by
  rcases hu with h | h
  · exact Or.inl h
  · exact Or.inr (in4_of_rIn hw h.2)

/-- Case 3.2 with the three triangles. -/
structure C32T (G : SimpleGraph V) (M : PlaneMap G) (v₀ v₁ v₂ v₃ z y x : V) (Ta Tb : Finset V) :
    Prop extends C32 G M v₀ v₁ v₂ v₃ z y x where
  hTa : G.IsNClique 3 Ta
  hTaA : ∀ u ∈ Ta, u ∈ c32Cl M z v₀ v₃ x
  hTb : G.IsNClique 3 Tb
  hTbB : ∀ u ∈ Tb, u ∈ c32Cl M z y v₂ v₁
  hcls : ∀ t : Finset V, G.IsNClique 3 t → t = {v₀, v₁, z} ∨ t = Ta ∨ t = Tb

theorem C32.toT (c : C32 G M v₀ v₁ v₂ v₃ z y x) : ∃ Ta Tb, C32T G M v₀ v₁ v₂ v₃ z y x Ta Tb := by
  obtain ⟨w₁, hw₁⟩ := c.in1_ne
  obtain ⟨w₂, hw₂⟩ := c.in2_ne
  obtain ⟨Ta, hTa, hTaA⟩ := c32_tri_side c.hG c.cyc1.extProp (in4_not_mem hw₁)
  obtain ⟨Tb, hTb, hTbB⟩ := c32_tri_side c.hG c.cyc2.extProp (in4_not_mem hw₂)
  have hA : ∀ u ∈ Ta, u ∈ c32Cl M z v₀ v₃ x := fun u hu => cl_of_rIn hw₁ (hTaA u hu)
  have hB : ∀ u ∈ Tb, u ∈ c32Cl M z y v₂ v₁ := fun u hu => cl_of_rIn hw₂ (hTbB u hu)
  have hT1 : G.IsNClique 3 ({v₀, v₁, z} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨c.a01, c.h0, c.h1⟩
  have n1a : ({v₀, v₁, z} : Finset V) ≠ Ta := fun h => c.v1_nA (hA v₁ (h ▸ by simp))
  have n1b : ({v₀, v₁, z} : Finset V) ≠ Tb := fun h => c.v0_nB (hB v₀ (h ▸ by simp))
  have nab : Ta ≠ Tb := by
    intro h
    have hsub : Ta ⊆ {z} := fun u hu => by
      simpa using c.disj (hA u hu) (hB u (h ▸ hu))
    have := Finset.card_le_card hsub
    rw [hTa.card_eq, Finset.card_singleton] at this
    omega
  exact ⟨Ta, Tb, ⟨c, hTa, hA, hTb, hB,
    fun t ht => c32_three_tri c.hG.tri hT1 hTa hTb n1a n1b nab ht⟩⟩

omit [Fintype V] in
theorem c32_not_sub1 {t : Finset V} {z : V} (ht : G.IsNClique 3 t) (h : ∀ u ∈ t, u = z) :
    False := by
  have hsub : t ⊆ {z} := fun u hu => by simpa using h u hu
  have := Finset.card_le_card hsub
  rw [ht.card_eq, Finset.card_singleton] at this
  omega

namespace C32T

variable {M : PlaneMap G} {v₀ v₁ v₂ v₃ z y x : V} {Ta Tb : Finset V}

theorem y_nA (c : C32T G M v₀ v₁ v₂ v₃ z y x Ta Tb) : y ∉ c32Cl M z v₀ v₃ x :=
  fun h => c.yz (c.disj h (Or.inl (by simp)))
theorem v2_nA (c : C32T G M v₀ v₁ v₂ v₃ z y x Ta Tb) : v₂ ∉ c32Cl M z v₀ v₃ x :=
  fun h => c.z2.symm (c.disj h (Or.inl (by simp)))
theorem x_nB (c : C32T G M v₀ v₁ v₂ v₃ z y x Ta Tb) : x ∉ c32Cl M z y v₂ v₁ :=
  fun h => c.xz (c.disj (Or.inl (by simp)) h)
theorem v3_nB (c : C32T G M v₀ v₁ v₂ v₃ z y x Ta Tb) : v₃ ∉ c32Cl M z y v₂ v₁ :=
  fun h => c.z3.symm (c.disj (Or.inl (by simp)) h)

theorem triA (c : C32T G M v₀ v₁ v₂ v₃ z y x Ta Tb) {t : Finset V} (ht : G.IsNClique 3 t)
    (hA : ∀ u ∈ t, u ∈ c32Cl M z v₀ v₃ x) : t = Ta := by
  rcases c.hcls t ht with rfl | h | rfl
  · exact absurd (hA v₁ (by simp)) c.v1_nA
  · exact h
  · exact (c32_not_sub1 ht fun u hu => c.disj (hA u hu) (c.hTbB u hu)).elim

theorem nxy (c : C32T G M v₀ v₁ v₂ v₃ z y x Ta Tb) : ¬ G.Adj x y := by
  intro hxy'
  have ht : G.IsNClique 3 ({z, x, y} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨c.hzx, c.hzy, hxy'⟩
  rcases c.hcls _ ht with h | h | h
  · have : x ∈ ({v₀, v₁, z} : Finset V) := h ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · exact c.x0 h
    · exact c.x1 h
    · exact c.xz h
  · exact c.y_nA (c.hTaA y (h ▸ by simp))
  · exact c.x_nB (c.hTbB x (h ▸ by simp))

theorem cover (c : C32T G M v₀ v₁ v₂ v₃ z y x Ta Tb) (u : V) :
    u ∈ c32Cl M z v₀ v₃ x ∨ u ∈ c32Cl M z y v₂ v₁ := by
  by_contra hu
  push Not at hu
  have hzA : z ∈ c32Cl M z v₀ v₃ x := Or.inl (by simp)
  have h3A : v₃ ∈ c32Cl M z v₀ v₃ x := Or.inl (by simp)
  have hxA : x ∈ c32Cl M z v₀ v₃ x := Or.inl (by simp)
  have h0A : v₀ ∈ c32Cl M z v₀ v₃ x := Or.inl (by simp)
  have hyB : y ∈ c32Cl M z y v₂ v₁ := Or.inl (by simp)
  have h2B : v₂ ∈ c32Cl M z y v₂ v₁ := Or.inl (by simp)
  have h1B : v₁ ∈ c32Cl M z y v₂ v₁ := Or.inl (by simp)
  have hext := c32_extProp_five c.hzy c.hy2 c.a23 c.hx3.symm c.hzx.symm
  have hu5 : u ∉ ({z, y, v₂, v₃, x} : Set V) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl | rfl | rfl | rfl)
    · exact hu.1 hzA
    · exact hu.2 hyB
    · exact hu.2 h2B
    · exact hu.1 h3A
    · exact hu.1 hxA
  obtain ⟨t, ht, htS⟩ := c32_tri_side c.hG hext hu5
  have key : ∀ w, RIn G ({z, y, v₂, v₃, x} : Set V)ᶜ u w →
      w ∉ c32Cl M z v₀ v₃ x ∧ w ∉ c32Cl M z y v₂ v₁ := by
    intro w hw
    induction hw with
    | refl => exact hu
    | @tail a b _ hst ih =>
      obtain ⟨hab, -, hb⟩ := hst
      have hb' : b ≠ z ∧ b ≠ y ∧ b ≠ v₂ ∧ b ≠ v₃ ∧ b ≠ x := by simpa using hb
      have hb0 : b ≠ v₀ := by
        rintro rfl
        exact ih.2 (c.nbr0 hab.symm (c.out1_of ih.1) ▸ h1B)
      have hb1 : b ≠ v₁ := by
        rintro rfl
        exact ih.1 (c.nbr1 hab.symm (c.out2_of ih.2) ▸ h0A)
      have ha1 : a ∉ ({z, v₀, v₃, x} : Set V) := fun h => ih.1 (Or.inl h)
      have ha2 : a ∉ ({z, y, v₂, v₁} : Set V) := fun h => ih.2 (Or.inl h)
      refine ⟨?_, ?_⟩
      · rintro (h | h)
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
          rcases h with h | h | h | h
          · exact hb'.1 h
          · exact hb0 h
          · exact hb'.2.2.2.1 h
          · exact hb'.2.2.2.2 h
        · exact ih.1 (Or.inr (in4_of_adj h hab.symm ha1))
      · rintro (h | h)
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
          rcases h with h | h | h | h
          · exact hb'.1 h
          · exact hb'.2.1 h
          · exact hb'.2.2.1 h
          · exact hb1 h
        · exact ih.2 (Or.inr (in4_of_adj h hab.symm ha2))
  rcases c.hcls t ht with rfl | rfl | rfl
  · rcases htS v₀ (by simp) with h | h
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h | h | h | h
      · exact c.z0 h.symm
      · exact c.y0 h.symm
      · exact c.d02 h
      · exact c.a30.ne h.symm
      · exact c.x0 h.symm
    · exact (key v₀ h.2).1 h0A
  · refine c.n3 (c32_adj_of_sub3 c.hTa (c := x) (fun w hw => ?_) c.z3)
    rcases htS w hw with h | h
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h | h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ c.hTaA w hw) c.y_nA
      · exact absurd (h ▸ c.hTaA w hw) c.v2_nA
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · exact absurd (c.hTaA w hw) (key w h.2).1
  · refine c.n2 (c32_adj_of_sub3 c.hTb (c := y) (fun w hw => ?_) c.z2)
    rcases htS w hw with h | h
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact absurd (h ▸ c.hTbB w hw) c.v3_nB
      · exact absurd (h ▸ c.hTbB w hw) c.x_nB
    · exact absurd (c.hTbB w hw) (key w h.2).2

theorem cross1 (c : C32T G M v₀ v₁ v₂ v₃ z y x Ta Tb) {a b : V} (hab : G.Adj a b)
    (ha : a ∈ c32Cl M z v₀ v₃ x) (haB : a ∉ c32Cl M z y v₂ v₁) (hb : b ∈ c32Cl M z y v₂ v₁)
    (hbA : b ∉ c32Cl M z v₀ v₃ x) : (a = v₀ ∧ b = v₁) ∨ (a = v₃ ∧ b = v₂) := by
  have haz : a ≠ z := fun h => haB (h ▸ Or.inl (by simp))
  have hbz : b ≠ z := fun h => hbA (h ▸ Or.inl (by simp))
  have ha1 : a ∈ ({z, v₀, v₃, x} : Set V) := by
    rcases ha with h | h
    · exact h
    · exfalso
      by_cases hb1 : b ∈ ({z, v₀, v₃, x} : Set V)
      · exact hbA (Or.inl hb1)
      · exact hbA (Or.inr (in4_of_adj h hab hb1))
  have hb2 : b ∈ ({z, y, v₂, v₁} : Set V) := by
    rcases hb with h | h
    · exact h
    · exfalso
      by_cases ha2 : a ∈ ({z, y, v₂, v₁} : Set V)
      · exact haB (Or.inl ha2)
      · exact haB (Or.inr (in4_of_adj h hab.symm ha2))
  have := c.n02; have := c.ny0; have := c.ny3; have := c.n13; have := c.nxy; have := c.nx2
  have := c.nx1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha1 hb2
  rcases ha1 with rfl | rfl | rfl | rfl <;> rcases hb2 with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl haz | exact absurd rfl hbz | exact Or.inl ⟨rfl, rfl⟩ |
      exact Or.inr ⟨rfl, rfl⟩ | exact absurd hab ‹_› | exact absurd hab.symm ‹_›

theorem false_of_common (c : C32T G M v₀ v₁ v₂ v₃ z y x Ta Tb)
    (hcommon : ∀ s ∈ c32Cl M z v₀ v₃ x, G.Adj z s → G.Adj v₃ s → s = v₀ ∨ s = x) : False := by
  refine c32_endgame c.hG (A := c32Cl M z v₀ v₃ x) (B := c32Cl M z y v₂ v₁) c.h0 c.a30 c.h1
    c.a12 c.a23 c.hzy c.hy2 c.z3 c.z2.symm (Or.inl (by simp)) (Or.inl (by simp))
    (Or.inl (by simp)) (Or.inl (by simp)) (Or.inl (by simp)) (Or.inl (by simp))
    (Or.inl (by simp)) (fun u ha hb => c.disj ha hb) ?_
    (card_edgeSet_restrict_lt c.a01 c.v0_nB) (fun t ht hA => c.triA ht hA) hcommon
  intro a b hab
  rcases c.cover a with ha | ha <;> rcases c.cover b with hb | hb
  · exact Or.inl ⟨ha, hb⟩
  · by_cases haB : a ∈ c32Cl M z y v₂ v₁
    · exact Or.inr (Or.inl ⟨haB, hb⟩)
    by_cases hbA : b ∈ c32Cl M z v₀ v₃ x
    · exact Or.inl ⟨ha, hbA⟩
    rcases c.cross1 hab ha haB hb hbA with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · by_cases hbB : b ∈ c32Cl M z y v₂ v₁
    · exact Or.inr (Or.inl ⟨ha, hbB⟩)
    by_cases haA : a ∈ c32Cl M z v₀ v₃ x
    · exact Or.inl ⟨haA, hb⟩
    rcases c.cross1 hab.symm hb hbB ha haA with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))))
  · exact Or.inr (Or.inl ⟨ha, hb⟩)

end C32T


section RB

variable {M : PlaneMap G} {v p q r t : V} {hp : G.Adj v p} {hq : G.Adj v q} {hr : G.Adj v r}
  {ht : G.Adj v t}

theorem rb_cyc (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (h : RBefore M ⟨(v, p), hp⟩ ⟨(v, q), hq⟩ ⟨(v, r), hr⟩) :
    RBefore M ⟨(v, q), hq⟩ ⟨(v, r), hr⟩ ⟨(v, p), hp⟩ :=
  rBefore_cyc M rfl rfl (c32_dne hpq _ _) (c32_dne hpr _ _) (c32_dne hqr _ _) h

theorem rb_trans (hqr : q ≠ r) (hrt : r ≠ t) (hqt : q ≠ t)
    (h1 : RBefore M ⟨(v, p), hp⟩ ⟨(v, q), hq⟩ ⟨(v, r), hr⟩)
    (h2 : RBefore M ⟨(v, p), hp⟩ ⟨(v, r), hr⟩ ⟨(v, t), ht⟩) :
    RBefore M ⟨(v, p), hp⟩ ⟨(v, q), hq⟩ ⟨(v, t), ht⟩ :=
  rBefore_trans M (a := ⟨(v, p), hp⟩) (b := ⟨(v, q), hq⟩) (c := ⟨(v, r), hr⟩) (d := ⟨(v, t), ht⟩)
    rfl rfl rfl (c32_dne hqr _ _) (c32_dne hrt _ _) (c32_dne hqt _ _) h1 h2

theorem rb_shift (hqr : q ≠ r) (hrt : r ≠ t) (hqt : q ≠ t)
    (h1 : RBefore M ⟨(v, p), hp⟩ ⟨(v, q), hq⟩ ⟨(v, r), hr⟩)
    (h2 : RBefore M ⟨(v, p), hp⟩ ⟨(v, r), hr⟩ ⟨(v, t), ht⟩) :
    RBefore M ⟨(v, q), hq⟩ ⟨(v, r), hr⟩ ⟨(v, t), ht⟩ :=
  rBefore_shift M (p := ⟨(v, p), hp⟩) (q := ⟨(v, q), hq⟩) (r := ⟨(v, r), hr⟩) (t := ⟨(v, t), ht⟩)
    rfl rfl rfl (c32_dne hqr _ _) (c32_dne hrt _ _) (c32_dne hqt _ _) h1 h2

end RB

omit [Fintype V] in
/-- Induction over the forward side of a 4-cycle, starting from the neighbours of the cycle. -/
theorem in4_induct {M : PlaneMap G} {a b c d : V} {R : V → Prop}
    (hbase : ∀ q u, q ∈ ({a, b, c, d} : Set V) → G.Adj q u → In4 M a b c d u → R u)
    (hstep : ∀ u u', In4 M a b c d u → R u → G.Adj u u' → u' ∉ ({a, b, c, d} : Set V) → R u') :
    ∀ w, In4 M a b c d w → R w := by
  rintro w ⟨hw, e, f, h1, h2, h3, h4, h5⟩
  have he : In4 M a b c d e.snd := ⟨h2, e, f, h1, h2, h3, h4, RIn.refl _⟩
  have key : ∀ u, RIn G ({a, b, c, d} : Set V)ᶜ e.snd u → In4 M a b c d u ∧ R u := by
    intro u hu
    induction hu with
    | refl => exact ⟨he, hbase _ _ h1 e.adj he⟩
    | @tail p q _ hst ih =>
      obtain ⟨hpq, -, hq⟩ := hst
      exact ⟨in4_of_adj ih.1 hpq hq, hstep p q ih.1 ih.2 hpq hq⟩
  exact (key w h5).2

omit [Fintype V] in
theorem c32_fin3_sub {S : Set V} {p q r : V} (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S) :
    ∀ u ∈ ({p, q, r} : Finset V), u ∈ S := by
  intro u hu
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with h | h | h <;> subst u <;> assumption

/-- Case 3.2 with an extra common neighbour `s` of `z` and `v₃` inside `z v₀ v₃ x`. -/
structure C32S (G : SimpleGraph V) (M : PlaneMap G) (v₀ v₁ v₂ v₃ z y x : V) (Ta Tb : Finset V)
    (s : V) : Prop extends C32T G M v₀ v₁ v₂ v₃ z y x Ta Tb where
  hsI : In4 M z v₀ v₃ x s
  hzs : G.Adj z s
  h3s : G.Adj v₃ s

namespace C32S

variable {M : PlaneMap G} {v₀ v₁ v₂ v₃ z y x : V} {Ta Tb : Finset V} {s : V}

theorem snm (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) : s ≠ z ∧ s ≠ v₀ ∧ s ≠ v₃ ∧ s ≠ x := by
  have := in4_not_mem c.hsI
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using this

theorem sz (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) : s ≠ z := c.snm.1
theorem s0 (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) : s ≠ v₀ := c.snm.2.1
theorem s3 (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) : s ≠ v₃ := c.snm.2.2.1
theorem sx (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) : s ≠ x := c.snm.2.2.2

theorem nadj_out (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) {w : V} (hw : In4 M x v₃ v₀ z w) :
    ¬ G.Adj s w := by
  intro h
  have hn : w ∉ ({z, v₀, v₃, x} : Set V) := by rw [set4_rev]; exact in4_not_mem hw
  exact c.cyc1.in4_disj M (in4_of_adj c.hsI h hn) hw

theorem ne_out (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) {w : V} (hw : In4 M x v₃ v₀ z w) :
    s ≠ w := fun h => c.cyc1.in4_disj M c.hsI (h ▸ hw)

theorem sA (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) : s ∈ c32Cl M z v₀ v₃ x := Or.inr c.hsI

theorem n0s (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) : ¬ G.Adj v₀ s := by
  intro h
  have hzA : z ∈ c32Cl M z v₀ v₃ x := Or.inl (by simp)
  have h0A : v₀ ∈ c32Cl M z v₀ v₃ x := Or.inl (by simp)
  have h3A : v₃ ∈ c32Cl M z v₀ v₃ x := Or.inl (by simp)
  have t1 : G.IsNClique 3 ({v₀, s, z} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨h, c.h0, c.hzs.symm⟩
  have t2 : G.IsNClique 3 ({v₀, s, v₃} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨h, c.a30.symm, c.h3s.symm⟩
  have e1 := c.triA t1 (c32_fin3_sub h0A c.sA hzA)
  have e2 := c.triA t2 (c32_fin3_sub h0A c.sA h3A)
  have : z ∈ ({v₀, s, v₃} : Finset V) := by rw [e2, ← e1]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h' | h' | h'
  · exact c.z0 h'
  · exact c.sz h'.symm
  · exact c.z3 h'

theorem nsx (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) : ¬ G.Adj s x := by
  intro h
  have hzA : z ∈ c32Cl M z v₀ v₃ x := Or.inl (by simp)
  have hxA : x ∈ c32Cl M z v₀ v₃ x := Or.inl (by simp)
  have h3A : v₃ ∈ c32Cl M z v₀ v₃ x := Or.inl (by simp)
  have t1 : G.IsNClique 3 ({s, x, z} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨h, c.hzs.symm, c.hzx.symm⟩
  have t2 : G.IsNClique 3 ({s, x, v₃} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨h, c.h3s.symm, c.hx3⟩
  have e1 := c.triA t1 (c32_fin3_sub c.sA hxA hzA)
  have e2 := c.triA t2 (c32_fin3_sub c.sA hxA h3A)
  have : z ∈ ({s, x, v₃} : Finset V) := by rw [e2, ← e1]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h' | h' | h'
  · exact c.sz h'.symm
  · exact c.xz h'.symm
  · exact c.z3 h'

theorem d1 (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) : Cyc4 G z v₀ v₃ s :=
  ⟨c.z0, c.z3, c.sz.symm, c.a30.ne.symm, c.s0.symm, c.s3.symm, c.h0.symm, c.a30.symm, c.h3s,
    c.hzs.symm⟩

theorem d2 (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) : Cyc4 G z s v₃ x :=
  ⟨c.sz.symm, c.z3, c.xz.symm, c.s3, c.sx, c.x3.symm, c.hzs, c.h3s.symm, c.hx3.symm,
    c.hzx.symm⟩

theorem rv3 (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) :
    RBefore M ⟨(v₃, s), c.h3s⟩ ⟨(v₃, x), c.hx3.symm⟩ ⟨(v₃, v₀), c.a30⟩ := by
  have h := c.hsI
  rw [in4_rot, in4_rot] at h
  exact c.cyc1.rot.rot.rBefore_of_in4 M h c.h3s

theorem rz (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) :
    RBefore M ⟨(z, s), c.hzs⟩ ⟨(z, v₀), c.h0.symm⟩ ⟨(z, x), c.hzx⟩ :=
  c.cyc1.rBefore_of_in4 M c.hsI c.hzs

theorem x_q1 (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) : In4 M s v₃ v₀ z x := by
  rw [in4_rot]
  exact c.d1.rev.rot.in4_of_rBefore M (e := ⟨(v₃, x), c.hx3.symm⟩) rfl
    (c32_nmem4 c.x3 c.x0 c.xz c.sx.symm) (rb_cyc c.sx c.s0 c.x0 c.rv3)

theorem v0_q2 (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) : In4 M x v₃ s z v₀ := by
  rw [in4_rot]
  exact c.d2.rev.rot.in4_of_rBefore M (e := ⟨(v₃, v₀), c.a30⟩) rfl
    (c32_nmem4 c.a30.ne.symm c.s0.symm c.z0.symm c.x0.symm)
    (rb_cyc c.x0 c.sx.symm c.s0.symm (rb_cyc c.sx c.s0 c.x0 c.rv3))

theorem p1sub (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) :
    ∀ w, In4 M z v₀ v₃ s w → In4 M z v₀ v₃ x w ∧ In4 M x v₃ s z w := by
  have hux : ∀ u, In4 M z v₀ v₃ s u → u ≠ x := fun u hu h => c.d1.in4_disj M hu (h ▸ c.x_q1)
  have hnm : ∀ u, In4 M z v₀ v₃ s u → u ≠ z ∧ u ≠ v₀ ∧ u ≠ v₃ ∧ u ≠ s := fun u hu => by
    have := in4_not_mem hu
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using this
  refine in4_induct (fun q u hq hqu hu => ?_) (fun u u' hu hR hadj hu' => ?_)
  · obtain ⟨uz, u0, u3, us⟩ := hnm u hu
    have ux := hux u hu
    have hS1 : u ∉ ({z, v₀, v₃, x} : Set V) := c32_nmem4 uz u0 u3 ux
    have hD2 : u ∉ ({x, v₃, s, z} : Set V) := c32_nmem4 ux u3 us uz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with hq | hq | hq | hq <;> subst q
    · have h1 := c.d1.rBefore_of_in4 M hu hqu
      have h2 := rb_cyc u0 us c.s0.symm h1
      have h3 := rb_cyc c.s0.symm u0.symm us.symm h2
      refine ⟨c.cyc1.in4_of_rBefore M (e := ⟨(z, u), hqu⟩) rfl hS1
        (rb_shift u0 c.x0.symm ux h3 c.rz), ?_⟩
      rw [in4_rot, in4_rot, in4_rot]
      exact c.d2.rev.rot.rot.rot.in4_of_rBefore M (e := ⟨(z, u), hqu⟩) rfl
        (c32_nmem4 uz ux u3 us) (rb_cyc us.symm c.sx ux (rb_trans u0 c.x0.symm ux h3 c.rz))
    · have hu' := hu
      rw [in4_rot] at hu'
      have h1 := c.d1.rot.rBefore_of_in4 M hu' hqu
      refine ⟨?_, in4_of_adj c.v0_q2 hqu hD2⟩
      rw [in4_rot]
      exact c.cyc1.rot.in4_of_rBefore M (e := ⟨(v₀, u), hqu⟩) rfl (c32_nmem4 u0 u3 ux uz) h1
    · have hu' := hu
      rw [in4_rot, in4_rot] at hu'
      have h1 := c.d1.rot.rot.rBefore_of_in4 M hu' hqu
      have h2 := rb_cyc us u0 c.s0 h1
      have h3 := rb_shift c.x0 u0.symm ux.symm c.rv3 h2
      have h4 := rb_cyc c.x0 ux.symm u0.symm h3
      have h5 := rb_cyc u0.symm c.x0.symm ux h4
      have h6 := rb_trans c.x0 u0.symm ux.symm c.rv3 h2
      have h7 := rb_cyc c.sx us.symm ux.symm h6
      have h8 := rb_cyc ux.symm c.sx.symm us h7
      refine ⟨?_, ?_⟩
      · rw [in4_rot, in4_rot]
        exact c.cyc1.rot.rot.in4_of_rBefore M (e := ⟨(v₃, u), hqu⟩) rfl
          (c32_nmem4 u3 ux uz u0) h5
      · rw [in4_rot]
        exact c.d2.rev.rot.in4_of_rBefore M (e := ⟨(v₃, u), hqu⟩) rfl
          (c32_nmem4 u3 us uz ux) h8
    · have hu' := hu
      rw [in4_rot, in4_rot, in4_rot] at hu'
      have h1 := c.d1.rot.rot.rot.rBefore_of_in4 M hu' hqu
      refine ⟨in4_of_adj c.hsI hqu hS1, ?_⟩
      rw [in4_rot, in4_rot]
      exact c.d2.rev.rot.rot.in4_of_rBefore M (e := ⟨(s, u), hqu⟩) rfl
        (c32_nmem4 us uz ux u3) h1
  · have hp' : In4 M z v₀ v₃ s u' := in4_of_adj hu hadj hu'
    obtain ⟨uz, u0, u3, us⟩ := hnm u' hp'
    have ux := hux u' hp'
    exact ⟨in4_of_adj hR.1 hadj (c32_nmem4 uz u0 u3 ux),
      in4_of_adj hR.2 hadj (c32_nmem4 ux u3 us uz)⟩

theorem p2sub (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) :
    ∀ w, In4 M z s v₃ x w → In4 M z v₀ v₃ x w := by
  have hu0 : ∀ u, In4 M z s v₃ x u → u ≠ v₀ := fun u hu h => c.d2.in4_disj M hu (h ▸ c.v0_q2)
  have hnm : ∀ u, In4 M z s v₃ x u → u ≠ z ∧ u ≠ s ∧ u ≠ v₃ ∧ u ≠ x := fun u hu => by
    have := in4_not_mem hu
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using this
  refine in4_induct (fun q u hq hqu hu => ?_) (fun u u' hu hR hadj hu' => ?_)
  · obtain ⟨uz, us, u3, ux⟩ := hnm u hu
    have u0 := hu0 u hu
    have hS1 : u ∉ ({z, v₀, v₃, x} : Set V) := c32_nmem4 uz u0 u3 ux
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with hq | hq | hq | hq <;> subst q
    · have h1 := c.d2.rBefore_of_in4 M hu hqu
      have h2 := rb_cyc us ux c.sx h1
      have h3 := rb_cyc c.sx us.symm ux.symm h2
      have g1 := rb_cyc c.s0 c.sx c.x0.symm c.rz
      have g2 := rb_cyc c.x0.symm c.s0.symm c.sx.symm g1
      have h4 := rb_trans us c.s0 u0 h3 g2
      exact c.cyc1.in4_of_rBefore M (e := ⟨(z, u), hqu⟩) rfl hS1 (rb_cyc ux.symm c.x0 u0 h4)
    · exact in4_of_adj c.hsI hqu hS1
    · have hu' := hu
      rw [in4_rot, in4_rot] at hu'
      have h1 := c.d2.rot.rot.rBefore_of_in4 M hu' hqu
      have h2 := rb_cyc ux us c.sx.symm h1
      have h3 := rb_cyc c.sx.symm ux.symm us.symm h2
      have h4 := rb_shift ux c.x0 u0 h3 c.rv3
      rw [in4_rot, in4_rot]
      exact c.cyc1.rot.rot.in4_of_rBefore M (e := ⟨(v₃, u), hqu⟩) rfl (c32_nmem4 u3 ux uz u0) h4
    · have hu' := hu
      rw [in4_rot, in4_rot, in4_rot] at hu'
      have h1 := c.d2.rot.rot.rot.rBefore_of_in4 M hu' hqu
      rw [in4_rot, in4_rot, in4_rot]
      exact c.cyc1.rot.rot.rot.in4_of_rBefore M (e := ⟨(x, u), hqu⟩) rfl
        (c32_nmem4 ux uz u0 u3) h1
  · have hp' : In4 M z s v₃ x u' := in4_of_adj hu hadj hu'
    obtain ⟨uz, us, u3, ux⟩ := hnm u' hp'
    exact in4_of_adj hR hadj (c32_nmem4 uz (hu0 u' hp') u3 ux)

theorem caseA (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) (hno : ∀ w, ¬ In4 M z v₀ v₃ s w) :
    False := by
  have hF1 := c.d1.fourFace M c.n3 c.n0s hno
  obtain ⟨-, m1, -, m3⟩ := hF1.mem_faceVerts
  have hN : ∀ u, G.Adj v₀ u → u = v₁ ∨ u = z ∨ u = v₃ :=
    c31_nbr_of_rot M c.d13 c.z3 ⟨(v₀, v₁), c.a01⟩ ⟨(v₀, z), c.h0⟩ ⟨(v₀, v₃), c.a30.symm⟩
      rfl rfl rfl rfl rfl rfl c.r01 (Or.inl hF1.f01) (Or.inl c.r03)
  refine c32_glue c.hG M _ hF1.inj m3 m1 c.s0 (fun h => c.n0s h.symm) hN c.a01 c.h0 c.h1
    c.hzs.symm c.h3s.symm c.n13 ?_
  intro t hst h1t
  by_contra htz
  obtain ⟨n0, n1, n2, n3⟩ := c.hF.mem_faceVerts
  exact no_crossing_paths_of_ne M _ c.hF.inj c.a01 c.a12 c.a23 c.a30 c.d02 c.d13 n0 n1 n2 n3
    c.h0 c.hzy c.hy2 h1t hst.symm c.h3s.symm ⟨c.z0, c.z1, c.z2, c.z3⟩ ⟨c.y0, c.y1, c.y2, c.y3⟩
    ⟨fun h => c.n0s (h ▸ hst.symm), h1t.ne.symm, fun h => c.nadj_out c.v2_out1 (h ▸ hst),
      fun h => c.n13 (h ▸ h1t)⟩
    ⟨c.s0, c.ne_out c.v1_out1, c.ne_out c.v2_out1, c.s3⟩ (Ne.symm htz) c.sz.symm
    (fun h => c.nadj_out c.y_out1 (h ▸ hst)) (c.ne_out c.y_out1).symm

theorem caseB (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) (hno : ∀ w, ¬ In4 M z s v₃ x w) :
    False := by
  have r1 : M.rot ⟨(x, v₃), c.hx3⟩ = ⟨(x, z), c.hzx.symm⟩ :=
    c.d2.rot.rot.rot.rot_eq_of_noadj M (fun h => c.nsx h.symm)
      (fun w _ hw => hno w (by rw [in4_rot] at hw; exact hw))
  have r2 : M.rot ⟨(x, z), c.hzx.symm⟩ = ⟨(x, v₃), c.hx3⟩ := by
    refine c.cyc1.rev.rot_eq_of_noadj M c.nx0 (fun w hxw hw => ?_)
    have hwA : w ∉ c32Cl M z v₀ v₃ x := by
      rintro (h | h)
      · exact in4_not_mem hw (set4_rev z v₀ v₃ x ▸ h)
      · exact c.cyc1.in4_disj M h hw
    rcases c.cover w with h | h
    · exact hwA h
    rcases h with h | h
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h | h | h
      · exact hwA (h ▸ Or.inl (by simp))
      · exact c.nxy (h ▸ hxw)
      · exact c.nx2 (h ▸ hxw)
      · exact c.nx1 (h ▸ hxw)
    · exact c.cyc2.in4_disj M (in4_of_adj h hxw.symm (c32_nmem4 c.xz c.hxy c.x2 c.x1)) c.x_out2
  have hN := c32_nbr_of_rot2 M c.hx3 c.hzx.symm r1 r2
  have h3 := c.hG.isCritical4.three_le_degree x
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at h3
  have h4 : (G.neighborFinset x).card ≤ ({v₃, z} : Finset V).card :=
    Finset.card_le_card fun u hu => by
      have := hN u ((SimpleGraph.mem_neighborFinset _ _ _).1 hu)
      simpa using this
  have h5 : ({v₃, z} : Finset V).card ≤ 2 := Finset.card_le_two
  omega

theorem caseC (c : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s) {w₁ w₂ : V}
    (h₁ : In4 M z v₀ v₃ s w₁) (h₂ : In4 M z s v₃ x w₂) : False := by
  obtain ⟨t1, ht1, ht1S⟩ := c32_tri_side c.hG c.d1.extProp (in4_not_mem h₁)
  obtain ⟨t2, ht2, ht2S⟩ := c32_tri_side c.hG c.d2.extProp (in4_not_mem h₂)
  have hu1 : ∀ u ∈ t1, u ∈ ({z, v₀, v₃, s} : Set V) ∨ In4 M z v₀ v₃ s u :=
    fun u hu => cl_of_rIn h₁ (ht1S u hu)
  have hu2 : ∀ u ∈ t2, u ∈ ({z, s, v₃, x} : Set V) ∨ In4 M z s v₃ x u :=
    fun u hu => cl_of_rIn h₂ (ht2S u hu)
  have hD1A : ∀ u ∈ ({z, v₀, v₃, s} : Set V), u ∈ c32Cl M z v₀ v₃ x := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with h | h | h | h <;> subst u
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact c.sA
  have hD2A : ∀ u ∈ ({z, s, v₃, x} : Set V), u ∈ c32Cl M z v₀ v₃ x := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with h | h | h | h <;> subst u
    · exact Or.inl (by simp)
    · exact c.sA
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
  have e1 := c.triA ht1 fun u hu =>
    (hu1 u hu).elim (hD1A u) (fun h => Or.inr (c.p1sub u h).1)
  have e2 := c.triA ht2 fun u hu => (hu2 u hu).elim (hD2A u) (fun h => Or.inr (c.p2sub u h))
  refine c.n3 (c32_adj_of_sub3 c.hTa (c := s) (fun u hu => ?_) c.z3)
  have a1 := hu1 u (e1 ▸ hu)
  have a2 := hu2 u (e2 ▸ hu)
  rcases a1 with h | h <;> rcases a2 with h' | h'
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h h'
    rcases h with h | h | h | h
    · exact Or.inl h
    · exfalso
      rw [h] at h'
      rcases h' with h' | h' | h' | h'
      · exact c.z0 h'.symm
      · exact c.s0 h'.symm
      · exact c.a30.ne h'.symm
      · exact c.x0 h'.symm
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exfalso
    have hn := in4_not_mem h'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h hn
    rcases h with h | h | h | h
    · exact hn.1 h
    · exact c.d2.in4_disj M h' (h ▸ c.v0_q2)
    · exact hn.2.2.1 h
    · exact hn.2.1 h
  · exfalso
    have hn := in4_not_mem h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h' hn
    rcases h' with h' | h' | h' | h'
    · exact hn.1 h'
    · exact hn.2.2.2 h'
    · exact hn.2.2.1 h'
    · exact c.d1.in4_disj M h (h' ▸ c.x_q1)
  · exact (c.d2.in4_disj M h' (c.p1sub u h).2).elim

end C32S

namespace C32T

variable {M : PlaneMap G} {v₀ v₁ v₂ v₃ z y x : V} {Ta Tb : Finset V}

theorem common (c : C32T G M v₀ v₁ v₂ v₃ z y x Ta Tb) :
    ∀ s ∈ c32Cl M z v₀ v₃ x, G.Adj z s → G.Adj v₃ s → s = v₀ ∨ s = x := by
  intro s hsA hzs h3s
  rcases hsA with h | h
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h | h
    · exact (hzs.ne h.symm).elim
    · exact Or.inl h
    · exact (h3s.ne h.symm).elim
    · exact Or.inr h
  · exfalso
    have cS : C32S G M v₀ v₁ v₂ v₃ z y x Ta Tb s := ⟨c, h, hzs, h3s⟩
    by_cases hA : ∃ w, In4 M z v₀ v₃ s w
    · by_cases hB : ∃ w, In4 M z s v₃ x w
      · obtain ⟨w₁, h₁⟩ := hA
        obtain ⟨w₂, h₂⟩ := hB
        exact cS.caseC h₁ h₂
      · push Not at hB
        exact cS.caseB hB
    · push Not at hA
      exact cS.caseA hA

end C32T

/-- **Case 3.2** (`x ≠ y`). -/
theorem GAMin.case32 (hG : GAMin G) (M : PlaneMap G) {e₀ e₁ e₂ e₃ : G.Dart}
    (hF : FourFace M e₀ e₁ e₂ e₃) {z y x : V} (h0 : G.Adj e₀.fst z) (h1 : G.Adj e₁.fst z)
    (hzy : G.Adj z y) (hy2 : G.Adj y e₂.fst) (hzx : G.Adj z x) (hx3 : G.Adj x e₃.fst)
    (n2 : ¬ G.Adj z e₂.fst) (n3 : ¬ G.Adj z e₃.fst) (ny0 : ¬ G.Adj y e₀.fst)
    (nx1 : ¬ G.Adj x e₁.fst) (hxy : x ≠ y) : False := by
  have s01 : e₀.snd = e₁.fst := by
    rw [← hF.f01, PlaneMap.facePerm_apply, M.isRotationSystem.fst_apply]; rfl
  have s12 : e₁.snd = e₂.fst := by
    rw [← hF.f12, PlaneMap.facePerm_apply, M.isRotationSystem.fst_apply]; rfl
  have s23 : e₂.snd = e₃.fst := by
    rw [← hF.f23, PlaneMap.facePerm_apply, M.isRotationSystem.fst_apply]; rfl
  have s30 : e₃.snd = e₀.fst := by
    rw [← hF.f30, PlaneMap.facePerm_apply, M.isRotationSystem.fst_apply]; rfl
  obtain ⟨⟨v₀, w₀⟩, a01⟩ := e₀
  obtain ⟨⟨v₁, w₁⟩, a12⟩ := e₁
  obtain ⟨⟨v₂, w₂⟩, a23⟩ := e₂
  obtain ⟨⟨v₃, w₃⟩, a30⟩ := e₃
  simp only at s01 s12 s23 s30 h0 h1 hy2 hx3 n2 n3 ny0 nx1
  subst w₀ w₁ w₂ w₃
  have n02 : ¬ G.Adj v₀ v₂ := hG.not_adj_of_fourFace M hF
  have n13 : ¬ G.Adj v₁ v₃ := hG.not_adj_of_fourFace M hF.rotate
  change G.Adj v₀ v₁ at a01
  change G.Adj v₁ v₂ at a12
  change G.Adj v₂ v₃ at a23
  change G.Adj v₃ v₀ at a30
  have z3 : z ≠ v₃ := fun h => n13 (h ▸ h1)
  have z2 : z ≠ v₂ := fun h => n02 (h ▸ h0)
  have d13 : v₁ ≠ v₃ := fun h => n3 (h ▸ h1.symm)
  have d02 : v₀ ≠ v₂ := fun h => n2 (h ▸ h0.symm)
  have r03 : M.rot ⟨(v₀, v₃), a30.symm⟩ = ⟨(v₀, v₁), a01⟩ := hF.f30
  have r10 : M.rot ⟨(v₁, v₀), a01.symm⟩ = ⟨(v₁, v₂), a12⟩ := hF.f01
  have r01 : M.rot ⟨(v₀, v₁), a01⟩ = ⟨(v₀, z), h0⟩ := by
    rcases c31_tri_rot hG M h0 h1.symm a01 ⟨(v₀, v₁), a01⟩ ⟨(v₀, z), h0⟩ rfl rfl rfl rfl with h | h
    · exact h
    · exact absurd (congrArg (fun d : G.Dart => d.snd) (M.rot.injective (h.trans r03.symm))) z3
  have r1z : M.rot ⟨(v₁, z), h1⟩ = ⟨(v₁, v₀), a01.symm⟩ := by
    rcases c31_tri_rot hG M a01.symm h0 h1 ⟨(v₁, z), h1⟩ ⟨(v₁, v₀), a01.symm⟩ rfl rfl rfl rfl
      with h | h
    · exact h
    · exact absurd (congrArg (fun d : G.Dart => d.snd) (h.symm.trans r10)) z2
  have hT : G.IsNClique 3 ({v₀, v₁, z} : Finset V) :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨a01, h0, h1⟩
  have nx0 : ¬ G.Adj x v₀ := by
    intro hx0
    have x1 : x ≠ v₁ := fun h => n13 (h ▸ hx3)
    refine c32_deg4 hG M (p₁ := v₃) (p₂ := v₁) (p₃ := z) (p₄ := x) a30.symm a01 h0 hx0.symm
      z3.symm x1.symm hzx.ne r03 r01 hzx hx3 hT (by simp)
      (c31_ne_of_mem (u := v₁) (by simp) (by simp [a01.ne.symm, h1.ne, x1.symm]))
      (c31_ne_of_mem (u := v₁) (by simp) (by
        simp [a01.ne.symm, x1.symm, d13]))
  have ny1 : ¬ G.Adj y v₁ := by
    intro hy1
    have y0 : y ≠ v₀ := fun h => n02 (h ▸ hy2)
    refine c32_deg4 hG M (p₁ := z) (p₂ := v₀) (p₃ := v₂) (p₄ := y) h1 a01.symm a12 hy1.symm
      z2 y0.symm hy2.ne.symm r1z r10 hy2.symm hzy.symm hT (by simp)
      (c31_ne_of_mem (u := v₀) (by simp) (by simp [a01.ne, d02, y0.symm]))
      (c31_ne_of_mem (u := v₀) (by simp) (by simp [a01.ne, y0.symm, h0.ne]))
  have nx2 : ¬ G.Adj x v₂ := fun hx2 => hG.case31 M hF h0 h1 hzx hx2 hx3 n2 n3 nx0 nx1
  have ny3 : ¬ G.Adj y v₃ := fun hy3 => hG.case31 M hF h0 h1 hzy hy2 hy3 n2 n3 ny0 ny1
  have c : C32 G M v₀ v₁ v₂ v₃ z y x := ⟨hG, a01, a12, a23, a30, hF, n02, n13, h0, h1, hzy, hy2,
    hzx, hx3, n2, n3, ny0, nx1, hxy, nx0, ny1, nx2, ny3, r03, r01, r1z, r10⟩
  obtain ⟨Ta, Tb, cT⟩ := c.toT
  exact cT.false_of_common cT.common

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
