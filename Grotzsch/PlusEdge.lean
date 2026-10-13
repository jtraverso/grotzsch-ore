/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Grotzsch.PlusVertex

/-!
# A triangle-free planar graph plus one edge is 3-colourable

**Theorem (Aksenov 1974; Jensen–Thomassen 2000; BKLY 2014, Theorem 2).** If `G` is a
triangle-free planar graph and `H` is obtained from `G` by adding one edge, then `H` is
3-colourable.

We follow Borodin–Kostochka–Lidický–Yancey (arXiv:1211.3981). Let `H = G + uv` be a counterexample
with the fewest vertices plus edges; it is 4-critical, so `3|E(H)| ≥ 5|V(H)| - 2`.
* **Case 1**: at most one face of `G` has length 4. Euler's formula gives `3|E(H)| ≤ 5|V| - 6`.
* **Case 2**: every 4-face has `u, v` as opposite corners and there are two of them,
  `u x₁ v x₂` and `u y₁ v y₂`. The `x`'s and `y`'s are distinct (a common one would be a vertex
  of degree 2, as the two faces would traverse the same path in opposite directions).
  Identifying `x₁` with `x₂` keeps `G` triangle-free: otherwise a path `x₁ q₁ q₂ x₂` exists, and
  it must contain `y₁` and `y₂` (`path_through_common_neighbour`, a `K₅`-minor argument with an
  apex inside the face), so `y₁ y₂` is an edge and `u y₁ y₂` a triangle.
* **Case 3**: some 4-face does not have `u, v` as opposite corners. One of the two identifications
  of opposite corners keeps `G` triangle-free (`no_crossing_paths`), and it maps `uv` to an edge.
In cases 2 and 3 the identified graph is again of the form (triangle-free planar) + one edge and
is smaller, hence 3-colourable, and so is `H`.

The topological "crossing" claims of the paper are replaced by `K₅`-minor arguments.
-/

@[expose] public section

noncomputable section

open Classical Finset Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

namespace Grotzsch

variable {V : Type} [Fintype V] {G : SimpleGraph V}

/-! ### Four-faces with explicit darts -/

/-- A face of length four, with its darts `d₀ → d₁ → d₂ → d₃ → d₀` and four distinct corners. -/
structure FourFace (M : PlaneMap G) (d₀ d₁ d₂ d₃ : G.Dart) : Prop where
  f01 : M.facePerm d₀ = d₁
  f12 : M.facePerm d₁ = d₂
  f23 : M.facePerm d₂ = d₃
  f30 : M.facePerm d₃ = d₀
  cover : ∀ e, SameCycle M.facePerm d₀ e → e = d₀ ∨ e = d₁ ∨ e = d₂ ∨ e = d₃
  ne02 : d₀.fst ≠ d₂.fst
  ne13 : d₁.fst ≠ d₃.fst

/-- A face with at most four darts in a triangle-free plane graph of minimum degree `≥ 2` is a
four-face. -/
theorem exists_fourFace (M : PlaneMap G) (h3 : G.CliqueFree 3) (hmin : ∀ v, 2 ≤ G.degree v)
    (d : G.Dart) (hd : Nat.card {e // SameCycle M.facePerm d e} ≤ 4) :
    ∃ d₁ d₂ d₃, FourFace M d d₁ d₂ d₃ := by
  have hσ := M.isRotationSystem
  have hdeg : ∀ v, 2 ≤ Nat.card {u // G.Adj v u} := fun v => by
    rw [show Nat.card {u // G.Adj v u} = Nat.card (G.neighborSet v) from rfl,
      Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]
    exact hmin v
  have fst_eq : ∀ e, (M.facePerm e).fst = e.snd := fun e => facePerm_fst hσ e
  have ne1 : ∀ e, M.facePerm e ≠ e := fun e => face_ne_self hσ e
  have ne2 : ∀ e, M.facePerm (M.facePerm e) ≠ e := fun e => face_face_ne_self hσ hdeg e
  have ne3 : ∀ e, M.facePerm (M.facePerm (M.facePerm e)) ≠ e :=
    fun e => face_three_ne_self_of_cliqueFree hσ h3 e
  -- the face permutation never sends a dart to its reverse
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
  obtain ⟨d1, hd1⟩ : ∃ d1, d1 = M.facePerm d := ⟨_, rfl⟩
  obtain ⟨d2, hd2⟩ : ∃ d2, d2 = M.facePerm d1 := ⟨_, rfl⟩
  obtain ⟨d3, hd3⟩ : ∃ d3, d3 = M.facePerm d2 := ⟨_, rfl⟩
  have m0 : SameCycle M.facePerm d d := SameCycle.refl _ _
  have m1 : SameCycle M.facePerm d d1 := hd1 ▸ sameCycle_apply_right.mpr m0
  have m2 : SameCycle M.facePerm d d2 := hd2 ▸ sameCycle_apply_right.mpr m1
  have m3 : SameCycle M.facePerm d d3 := hd3 ▸ sameCycle_apply_right.mpr m2
  have a1 : d1 ≠ d := hd1 ▸ ne1 d
  have a2 : d2 ≠ d := by rw [hd2, hd1]; exact ne2 d
  have a3 : d3 ≠ d := by rw [hd3, hd2, hd1]; exact ne3 d
  have a4 : d2 ≠ d1 := hd2 ▸ ne1 d1
  have a5 : d3 ≠ d1 := by rw [hd3, hd2]; exact ne2 d1
  have a6 : d3 ≠ d2 := hd3 ▸ ne1 d2
  -- the four darts form the whole face
  set O := Finset.univ.filter fun e => SameCycle M.facePerm d e
  have hO : O.card ≤ 4 := by
    have := hd
    rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
  have hS : ({d, d1, d2, d3} : Finset G.Dart).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [a1.symm, a2.symm, a3.symm]),
      Finset.card_insert_of_notMem (by simp [a4.symm, a5.symm]),
      Finset.card_insert_of_notMem (by simp [a6.symm]), Finset.card_singleton]
  have hSO : ({d, d1, d2, d3} : Finset G.Dart) ⊆ O := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;> simp [O, *]
  have hEq := Finset.eq_of_subset_of_card_le hSO (by omega)
  have cover : ∀ e, SameCycle M.facePerm d e → e = d ∨ e = d1 ∨ e = d2 ∨ e = d3 := by
    intro e he
    have : e ∈ O := by simp [O, he]
    rw [← hEq] at this
    simpa using this
  have h4 : M.facePerm d3 = d := by
    rcases cover _ (sameCycle_apply_right.mpr m3) with h | h | h | h
    · exact h
    · exact absurd (M.facePerm.injective (h.trans hd1)) a3
    · exact absurd (M.facePerm.injective (h.trans hd2)) a5
    · exact absurd h (ne1 d3)
  -- the vertices of the face
  have e1 : d1.fst = d.snd := hd1 ▸ fst_eq d
  have e2 : d2.fst = d1.snd := hd2 ▸ fst_eq d1
  have e3 : d3.fst = d2.snd := hd3 ▸ fst_eq d2
  have e4 : d.fst = d3.snd := by rw [← h4]; exact fst_eq d3
  have hxy : G.Adj d.fst d1.fst := e1 ▸ d.adj
  have hyz : G.Adj d1.fst d2.fst := e2 ▸ d1.adj
  have hzu : G.Adj d2.fst d3.fst := e3 ▸ d2.adj
  have hux : G.Adj d3.fst d.fst := e4 ▸ d3.adj
  have hxz : d.fst ≠ d2.fst := by
    intro h
    apply nosymm d
    rw [← hd1, SimpleGraph.Dart.ext_iff, Prod.ext_iff]
    simp only [SimpleGraph.Dart.symm_toProd, Prod.fst_swap, Prod.snd_swap]
    exact ⟨e1, by rw [← e2, ← h]⟩
  have hyu : d1.fst ≠ d3.fst := by
    intro h
    apply nosymm d1
    rw [← hd2, SimpleGraph.Dart.ext_iff, Prod.ext_iff]
    simp only [SimpleGraph.Dart.symm_toProd, Prod.fst_swap, Prod.snd_swap]
    exact ⟨e2, by rw [← e3, ← h]⟩
  exact ⟨d1, d2, d3, hd1.symm, hd2.symm, hd3.symm, h4, cover, hxz, hyu⟩

namespace FourFace

variable {M : PlaneMap G} {d₀ d₁ d₂ d₃ : G.Dart}

theorem snd₀ (h : FourFace M d₀ d₁ d₂ d₃) : d₀.snd = d₁.fst := by
  rw [← h.f01]; exact (facePerm_fst M.isRotationSystem d₀).symm
theorem snd₁ (h : FourFace M d₀ d₁ d₂ d₃) : d₁.snd = d₂.fst := by
  rw [← h.f12]; exact (facePerm_fst M.isRotationSystem d₁).symm
theorem snd₂ (h : FourFace M d₀ d₁ d₂ d₃) : d₂.snd = d₃.fst := by
  rw [← h.f23]; exact (facePerm_fst M.isRotationSystem d₂).symm
theorem snd₃ (h : FourFace M d₀ d₁ d₂ d₃) : d₃.snd = d₀.fst := by
  rw [← h.f30]; exact (facePerm_fst M.isRotationSystem d₃).symm

theorem adj₀ (h : FourFace M d₀ d₁ d₂ d₃) : G.Adj d₀.fst d₁.fst := h.snd₀ ▸ d₀.adj
theorem adj₁ (h : FourFace M d₀ d₁ d₂ d₃) : G.Adj d₁.fst d₂.fst := h.snd₁ ▸ d₁.adj
theorem adj₂ (h : FourFace M d₀ d₁ d₂ d₃) : G.Adj d₂.fst d₃.fst := h.snd₂ ▸ d₂.adj
theorem adj₃ (h : FourFace M d₀ d₁ d₂ d₃) : G.Adj d₃.fst d₀.fst := h.snd₃ ▸ d₃.adj

theorem same₁ (h : FourFace M d₀ d₁ d₂ d₃) : SameCycle M.facePerm d₀ d₁ :=
  h.f01 ▸ sameCycle_apply_right.mpr (SameCycle.refl _ _)
theorem same₂ (h : FourFace M d₀ d₁ d₂ d₃) : SameCycle M.facePerm d₀ d₂ :=
  h.f12 ▸ sameCycle_apply_right.mpr h.same₁
theorem same₃ (h : FourFace M d₀ d₁ d₂ d₃) : SameCycle M.facePerm d₀ d₃ :=
  h.f23 ▸ sameCycle_apply_right.mpr h.same₂

/-- The face is vertex-injective. -/
theorem inj (h : FourFace M d₀ d₁ d₂ d₃) :
    ∀ e e' : FaceApex.F M d₀, e.1.fst = e'.1.fst → e = e' := by
  have b1 := h.adj₀.ne; have b2 := h.adj₁.ne; have b3 := h.adj₂.ne; have b4 := h.adj₃.ne
  have b5 := h.ne02; have b6 := h.ne13
  rintro ⟨e, he⟩ ⟨e', he'⟩ hfst
  apply Subtype.ext
  simp only at hfst ⊢
  rcases h.cover e he with rfl | rfl | rfl | rfl <;>
    rcases h.cover e' he' with rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | exact absurd hfst b1 | exact absurd hfst.symm b1
    | exact absurd hfst b2 | exact absurd hfst.symm b2
    | exact absurd hfst b3 | exact absurd hfst.symm b3
    | exact absurd hfst b4 | exact absurd hfst.symm b4
    | exact absurd hfst b5 | exact absurd hfst.symm b5
    | exact absurd hfst b6 | exact absurd hfst.symm b6

/-- The corners lie on the face. -/
theorem mem_faceVerts (h : FourFace M d₀ d₁ d₂ d₃) :
    d₀.fst ∈ FaceApex.faceVerts M d₀ ∧ d₁.fst ∈ FaceApex.faceVerts M d₀ ∧
      d₂.fst ∈ FaceApex.faceVerts M d₀ ∧ d₃.fst ∈ FaceApex.faceVerts M d₀ :=
  ⟨⟨⟨d₀, SameCycle.refl _ _⟩, rfl⟩, ⟨⟨d₁, h.same₁⟩, rfl⟩, ⟨⟨d₂, h.same₂⟩, rfl⟩,
    ⟨⟨d₃, h.same₃⟩, rfl⟩⟩

/-- Rotating the labels of a four-face gives a four-face (with the same face). -/
theorem rotate (h : FourFace M d₀ d₁ d₂ d₃) : FourFace M d₁ d₂ d₃ d₀ :=
  ⟨h.f12, h.f23, h.f30, h.f01,
    fun e he => by
      rcases h.cover e (h.same₁.trans he) with h' | h' | h' | h'
      · exact Or.inr (Or.inr (Or.inr h'))
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inl h')),
    h.ne13, h.ne02.symm⟩

end FourFace

/-! ### Degree-two vertices from the rotation -/

/-- If the rotation swaps two distinct darts at a vertex, the vertex has at most two
neighbours. -/
theorem card_adj_le_two_of_rot_swap (M : PlaneMap G) {e₁ e₂ : G.Dart}
    (h12 : M.rot e₁ = e₂) (h21 : M.rot e₂ = e₁) : Nat.card {u // G.Adj e₁.fst u} ≤ 2 := by
  have h1 := card_neighbor_le_card_sameCycle M.isRotationSystem e₁
  have hinv1 : M.rot⁻¹ e₁ = e₂ := by rw [Perm.inv_eq_iff_eq]; exact h21.symm
  have hinv2 : M.rot⁻¹ e₂ = e₁ := by rw [Perm.inv_eq_iff_eq]; exact h12.symm
  have hmem : ∀ i : ℤ, (M.rot ^ i) e₁ = e₁ ∨ (M.rot ^ i) e₁ = e₂ := by
    intro i
    induction i using Int.induction_on with
    | zero => simp
    | succ i ih =>
      rw [add_comm, zpow_add, zpow_one, Perm.mul_apply]
      rcases ih with h | h <;> rw [h]
      · exact Or.inr h12
      · exact Or.inl h21
    | pred i ih =>
      rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one, Perm.mul_apply]
      rcases ih with h | h <;> rw [h]
      · exact Or.inr hinv1
      · exact Or.inl hinv2
  have h2 : Nat.card {e // SameCycle M.rot e₁ e} ≤ 2 := by
    have hb : Nat.card Bool = 2 := by simp
    rw [← hb]
    refine Nat.card_le_card_of_injective (fun e => decide (e.1 = e₁)) fun a b hab => ?_
    obtain ⟨ia, ha⟩ := a.2
    obtain ⟨ib, hb⟩ := b.2
    apply Subtype.ext
    rcases hmem ia with ha' | ha' <;> rcases hmem ib with hb' | hb' <;>
      simp_all
  omega

/-- Two faces traversing the path `u z v` in opposite directions force `z` to have degree at
most two. -/
theorem card_adj_le_two_of_opposite (M : PlaneMap G) {u z v : V} (huz : G.Adj u z)
    (hzv : G.Adj z v)
    (h1 : M.facePerm ⟨(u, z), huz⟩ = ⟨(z, v), hzv⟩)
    (h2 : M.facePerm ⟨(v, z), hzv.symm⟩ = ⟨(z, u), huz.symm⟩) :
    Nat.card {w // G.Adj z w} ≤ 2 := by
  rw [PlaneMap.facePerm_apply] at h1 h2
  exact card_adj_le_two_of_rot_swap M (e₁ := ⟨(z, u), huz.symm⟩) (e₂ := ⟨(z, v), hzv⟩) h1 h2

/-! ### Euler's formula with one exceptional face -/

/-- Counting classes from below with one exceptional class: if every class has at least four
elements and all classes of size four coincide, then `5 · #classes ≤ |α| + 1`. -/
theorem five_mul_numClasses_le_add_one {α : Type*} [Finite α] (s : Setoid α)
    (h4 : ∀ a, 4 ≤ Nat.card {b // s a b})
    (h5 : ∀ a a', Nat.card {b // s a b} = 4 → Nat.card {b // s a' b} = 4 → s a a') :
    5 * numClasses s ≤ Nat.card α + 1 := by
  classical
  have := Fintype.ofFinite α
  by_cases hex : ∃ a, Nat.card {b // s a b} = 4
  · obtain ⟨a₀, ha₀⟩ := hex
    have hsum := Finset.card_eq_sum_card_fiberwise
      (f := Quotient.mk s) (s := (Finset.univ : Finset α)) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    have hcard : ∀ a, (Finset.univ.filter fun b => Quotient.mk s b = Quotient.mk s a).card =
        Nat.card {b // s a b} := by
      intro a
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => s.symm (Quotient.exact h), fun h => Quotient.sound (s.symm h)⟩
    have hfib : ∀ q : Quotient s, 5 ≤ (Finset.univ.filter fun a => Quotient.mk s a = q).card +
        (if q = Quotient.mk s a₀ then 1 else 0) := by
      intro q
      induction q using Quotient.inductionOn with
      | h a =>
      rw [hcard a]
      have := h4 a
      by_cases ha : Nat.card {b // s a b} = 4
      · have hq : Quotient.mk s a = Quotient.mk s a₀ := Quotient.sound (s.symm (h5 a₀ a ha₀ ha))
        rw [if_pos hq]; omega
      · omega
    have hle : ∑ q : Quotient s, 5 ≤ ∑ q : Quotient s,
        ((Finset.univ.filter fun a => Quotient.mk s a = q).card +
          (if q = Quotient.mk s a₀ then 1 else 0)) :=
      Finset.sum_le_sum fun q _ => hfib q
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq'] at hle
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.mem_univ, if_true] at hle
    simp only [numClasses, Nat.card_eq_fintype_card]
    rw [Finset.card_univ] at hsum
    rw [mul_comm]
    omega
  · push Not at hex
    have := mul_numClasses_le s 5 fun a => by
      have := h4 a; have := hex a; omega
    omega

/-- If every face has at least four darts and all but at most one have at least five, and there
are no isolated vertices, then `3|E| + 9 ≤ 5|V|`. -/
theorem three_mul_card_edgeSet_add_nine_le (M : PlaneMap G) [Nonempty G.Dart]
    (hiso : ∀ v, ∃ u, G.Adj v u)
    (h4 : ∀ d : G.Dart, 4 ≤ Nat.card {e // SameCycle M.facePerm d e})
    (h5 : ∀ d d' : G.Dart, Nat.card {e // SameCycle M.facePerm d e} = 4 →
      Nat.card {e // SameCycle M.facePerm d' e} = 4 → SameCycle M.facePerm d d') :
    3 * Nat.card G.edgeSet + 9 ≤ 5 * Fintype.card V := by
  have h0 := M.eulerDefect_eq_zero
  have hα := card_dart_eq_two_mul G
  have hE := card_edgeSet_eq_cycleCount (G := G)
  have hφ : 5 * cycleCount (M.rot * dartSymm _) ≤ Nat.card G.Dart + 1 :=
    five_mul_numClasses_le_add_one _ (fun d => h4 d) (fun d d' hd hd' => h5 d d' hd hd')
  have hK := one_le_numComponents M.rot (dartSymm G)
  have hn := cycleCount_eq_card_nonisolated M.isRotationSystem
  have hn' : Nat.card {v // ∃ u, G.Adj v u} = Fintype.card V := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hiso), Nat.card_eq_fintype_card]
  unfold eulerDefect at h0
  omega

/-! ### Paths across a face must pass through every other common neighbour -/

/-- Let `u x₁ v x₂` be the corners of a vertex-injective face, and `y` another common neighbour of
`u` and `v`. A path `x₁ q₁ q₂ x₂` avoiding `u`, `v` passes through `y`: otherwise the apex inside
the face, `{u, y}`, `{v}`, `{x₁, q₁, q₂}` and `{x₂}` would form a `K₅` minor of a planar graph. -/
theorem path_through_common_neighbour (M : PlaneMap G) (o : G.Dart)
    (hinj : ∀ e e' : FaceApex.F M o, e.1.fst = e'.1.fst → e = e')
    {u x₁ v x₂ y q₁ q₂ : V}
    (hu : u ∈ FaceApex.faceVerts M o) (hx₁ : x₁ ∈ FaceApex.faceVerts M o)
    (hv : v ∈ FaceApex.faceVerts M o) (hx₂ : x₂ ∈ FaceApex.faceVerts M o)
    (hux₁ : G.Adj u x₁) (hux₂ : G.Adj u x₂) (hvx₁ : G.Adj v x₁) (hvx₂ : G.Adj v x₂)
    (huy : G.Adj u y) (hvy : G.Adj v y)
    (hx₁q₁ : G.Adj x₁ q₁) (hq₁q₂ : G.Adj q₁ q₂) (hq₂x₂ : G.Adj q₂ x₂)
    (hy : y ≠ x₁ ∧ y ≠ x₂ ∧ y ≠ q₁ ∧ y ≠ q₂)
    (hq : q₁ ≠ u ∧ q₁ ≠ v ∧ q₂ ≠ u ∧ q₂ ≠ v) (hxx : x₁ ≠ x₂) (huv : u ≠ v)
    (hq₁x₂ : q₁ ≠ x₂) : False := by
  obtain ⟨hyx₁, hyx₂, hyq₁, hyq₂⟩ := hy
  obtain ⟨hq₁u, hq₁v, hq₂u, hq₂v⟩ := hq
  have n1 := hux₁.ne; have n2 := hux₂.ne; have n3 := hvx₁.ne; have n4 := hvx₂.ne
  have n5 := huy.ne; have n6 := hvy.ne; have n7 := hx₁q₁.ne; have n8 := hq₂x₂.ne
  have m1 := n1.symm; have m2 := n2.symm; have m3 := n3.symm; have m4 := n4.symm
  have m5 := n5.symm; have m6 := n6.symm; have m7 := n7.symm; have m8 := n8.symm
  have m9 := hyx₁.symm; have m10 := hyx₂.symm; have m11 := hyq₁.symm; have m12 := hyq₂.symm
  have m13 := hq₁u.symm; have m14 := hq₁v.symm; have m15 := hq₂u.symm; have m16 := hq₂v.symm
  have m17 := hxx.symm; have m18 := huv.symm; have m19 := hq₁x₂.symm
  set A := apexExtend G (FaceApex.faceVerts M o)
  have hP := isPlanar_apexExtend_face M o hinj
  have conn2 : ∀ p q : V, G.Adj p q →
      (A.induce (↑({some p, some q} : Finset (Option V)) : Set (Option V))).Connected := by
    intro p q hpq
    rw [← connSet_iff_induce_connected]
    have := (connSet_singleton A (some q)).insert_adj (a := some p) (Set.mem_singleton _) hpq
    simpa using this
  have conn3 : (A.induce (↑({some x₁, some q₁, some q₂} : Finset (Option V)) :
      Set (Option V))).Connected := by
    rw [← connSet_iff_induce_connected]
    have h1 := (connSet_singleton A (some q₂)).insert_adj (a := some q₁) (Set.mem_singleton _) hq₁q₂
    have h2 := h1.insert_adj (a := some x₁) (Set.mem_insert _ _) hx₁q₁
    simpa using h2
  let br : Fin 5 → Finset (Option V) :=
    ![{none}, {some u, some y}, {some v}, {some x₁, some q₁, some q₂}, {some x₂}]
  refine cliqueMinorFree_five_of_isPlanar hP ⟨{
    branch := br
    branch_nonempty := fun i => by fin_cases i <;> simp [br]
    branch_connected := fun i => ?_
    branch_disjoint := fun i j hij => ?_
    branch_adjacent := fun i j hij => ?_ }⟩
  · fin_cases i
    · rw [← connSet_iff_induce_connected]; simpa [br] using connSet_singleton A none
    · exact conn2 u y huy
    · rw [← connSet_iff_induce_connected]; simpa [br] using connSet_singleton A (some v)
    · exact conn3
    · rw [← connSet_iff_induce_connected]; simpa [br] using connSet_singleton A (some x₂)
  · rw [Finset.disjoint_left]
    fin_cases i <;> fin_cases j <;> simp_all [br]
  · have key : ∀ i j : Fin 5, i < j → ∃ p ∈ br i, ∃ q ∈ br j, A.Adj p q := by
      intro i j hlt
      fin_cases i <;> fin_cases j <;> first | (exfalso; revert hlt; decide) | skip
      · exact ⟨none, by simp [br], some u, by simp [br], hu⟩
      · exact ⟨none, by simp [br], some v, by simp [br], hv⟩
      · exact ⟨none, by simp [br], some x₁, by simp [br], hx₁⟩
      · exact ⟨none, by simp [br], some x₂, by simp [br], hx₂⟩
      · exact ⟨some y, by simp [br], some v, by simp [br], hvy.symm⟩
      · exact ⟨some u, by simp [br], some x₁, by simp [br], hux₁⟩
      · exact ⟨some u, by simp [br], some x₂, by simp [br], hux₂⟩
      · exact ⟨some v, by simp [br], some x₁, by simp [br], hvx₁⟩
      · exact ⟨some v, by simp [br], some x₂, by simp [br], hvx₂⟩
      · exact ⟨some q₂, by simp [br], some x₂, by simp [br], hq₂x₂⟩
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · obtain ⟨p, hp, q, hq, hpq⟩ := key j i h
      exact ⟨q, hq, p, hp, hpq.symm⟩

/-! ### Auxiliary lemmas for the main theorem -/

private lemma pe_card_edgeSet_induce_le (H : SimpleGraph V) (s : Set V) :
    Nat.card (H.induce s).edgeSet ≤ Nat.card H.edgeSet := by
  refine Nat.card_le_card_of_injective
    (fun e => ⟨Sym2.map Subtype.val e.1, ?_⟩) fun e₁ e₂ h => ?_
  · obtain ⟨e, he⟩ := e
    induction e using Sym2.ind with
    | _ a b => simpa using he
  · exact Subtype.ext (Sym2.map.injective Subtype.val_injective (congrArg Subtype.val h))

omit [Fintype V] in
private lemma pe_adj_of_ne {H : SimpleGraph V} {u v a b : V} (h : H.Adj a b)
    (hne : s(a, b) ≠ s(u, v)) : (H.deleteEdges {s(u, v)}).Adj a b := by
  simp [SimpleGraph.deleteEdges_adj, h, hne]

private lemma pe_card_edgeSet_le (H : SimpleGraph V) (e : Sym2 V) :
    Nat.card H.edgeSet ≤ Nat.card (H.deleteEdges {e}).edgeSet + 1 := by
  rw [SimpleGraph.edgeSet_deleteEdges, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  have := Set.ncard_le_ncard_sdiff_add_ncard H.edgeSet {e}
  simpa using this

private lemma pe_card_adj_le (H : SimpleGraph V) {u v z : V} (hzu : z ≠ u) (hzv : z ≠ v) :
    Nat.card {w // H.Adj z w} ≤ Nat.card {w // (H.deleteEdges {s(u, v)}).Adj z w} :=
  Nat.card_le_card_of_injective (fun w => ⟨w.1, pe_adj_of_ne w.2 (by simp [hzu, hzv])⟩)
    (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))

private lemma pe_card_adj_le_succ (H : SimpleGraph V) (u v z : V) :
    Nat.card {w // H.Adj z w} ≤ Nat.card {w // (H.deleteEdges {s(u, v)}).Adj z w} + 1 := by
  rw [← Finite.card_option]
  refine Nat.card_le_card_of_injective (fun w =>
    if h : (H.deleteEdges {s(u, v)}).Adj z w.1 then some ⟨w.1, h⟩ else none) ?_
  intro a b hab
  by_cases ha : (H.deleteEdges {s(u, v)}).Adj z a.1 <;>
    by_cases hb : (H.deleteEdges {s(u, v)}).Adj z b.1 <;> simp only [ha, hb, dite_true,
      dite_false, Option.some.injEq, reduceCtorEq] at hab
  · exact Subtype.ext (Subtype.mk.inj hab)
  · have h1 : s(z, a.1) = s(u, v) := by
      by_contra h; exact ha (pe_adj_of_ne a.2 h)
    have h2 : s(z, b.1) = s(u, v) := by
      by_contra h; exact hb (pe_adj_of_ne b.2 h)
    exact Subtype.ext (Sym2.congr_right.mp (h1.trans h2.symm))

omit [Fintype V] in
private lemma pe_card_adj_eq_degree (G : SimpleGraph V) (z : V) [Fintype (G.neighborSet z)] :
    Nat.card {w // G.Adj z w} = G.degree z := by
  rw [show Nat.card {w // G.Adj z w} = Nat.card (G.neighborSet z) from rfl,
    Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]

private lemma pe_isCritical4 {n : ℕ}
    (ih : ∀ m < n, ∀ (V : Type) [Fintype V] (H : SimpleGraph V) (u v : V),
      Fintype.card V + Nat.card H.edgeSet = m → u ≠ v →
      IsPlanar (H.deleteEdges {s(u, v)}) → (H.deleteEdges {s(u, v)}).CliqueFree 3 →
      H.Colorable 3)
    (H : SimpleGraph V) {u v : V} (hn : Fintype.card V + Nat.card H.edgeSet = n) (huv : u ≠ v)
    (hP : IsPlanar (H.deleteEdges {s(u, v)})) (h3 : (H.deleteEdges {s(u, v)}).CliqueFree 3)
    (hcol : ¬ H.Colorable 3) : IsCritical4 H := by
  refine ⟨hcol, fun w => ?_, fun e he => ?_⟩
  · by_cases hwu : w = u
    · subst hwu
      have hT := planar_cliqueFree_of_injective (X := H.induce {x | x ≠ w})
        (Y := H.deleteEdges {s(w, v)}) Subtype.val Subtype.val_injective
        (fun a b h => pe_adj_of_ne h (by
          simp only [ne_eq, Sym2.eq_iff, not_or, not_and]
          exact ⟨fun h => absurd h a.2, fun _ h => absurd h b.2⟩))
      exact grotzsch _ (hT.1 hP) (hT.2 h3)
    by_cases hwv : w = v
    · subst hwv
      have hT := planar_cliqueFree_of_injective (X := H.induce {x | x ≠ w})
        (Y := H.deleteEdges {s(u, w)}) Subtype.val Subtype.val_injective
        (fun a b h => pe_adj_of_ne h (by
          simp only [ne_eq, Sym2.eq_iff, not_or, not_and]
          exact ⟨fun _ h => absurd h b.2, fun h => absurd h a.2⟩))
      exact grotzsch _ (hT.1 hP) (hT.2 h3)
    have hcard : Fintype.card {x | x ≠ w} < Fintype.card V :=
      Fintype.card_subtype_lt (p := fun x => x ≠ w) (x := w) (by simp)
    have hedge := pe_card_edgeSet_induce_le H {x | x ≠ w}
    let u₁ : {x | x ≠ w} := ⟨u, fun h => hwu h.symm⟩
    let v₁ : {x | x ≠ w} := ⟨v, fun h => hwv h.symm⟩
    have hT := planar_cliqueFree_of_injective
      (X := (H.induce {x | x ≠ w}).deleteEdges {s(u₁, v₁)})
      (Y := H.deleteEdges {s(u, v)}) Subtype.val Subtype.val_injective
      (fun a b h => by
        rw [SimpleGraph.deleteEdges_adj] at h
        refine pe_adj_of_ne h.1 fun he => h.2 ?_
        simp only [Set.mem_singleton_iff, Sym2.eq_iff] at he ⊢
        rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
        · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩)
    exact ih _ (by omega) _ (H.induce {x | x ≠ w}) u₁ v₁ rfl
      (fun h => huv (congrArg Subtype.val h)) (hT.1 hP) (hT.2 h3)
  · by_cases heuv : e = s(u, v)
    · subst heuv
      exact grotzsch _ hP h3
    have hlt : Nat.card (H.deleteEdges {e}).edgeSet < Nat.card H.edgeSet := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
      refine LE.le.ssubset_of_ne
        (SimpleGraph.edgeSet_mono (H.deleteEdges_le _)) fun h => ?_
      have : e ∈ (H.deleteEdges {e}).edgeSet := by rw [h]; exact he
      simp at this
    have hT := planar_cliqueFree_of_injective
      (X := (H.deleteEdges {e}).deleteEdges {s(u, v)}) (Y := H.deleteEdges {s(u, v)})
      id Function.injective_id (fun a b h => by
        simp only [SimpleGraph.deleteEdges_adj] at h ⊢
        exact ⟨h.1.1, h.2⟩)
    exact ih _ (by omega) V (H.deleteEdges {e}) u v rfl huv (hT.1 hP) (hT.2 h3)

private lemma pe_glue_step {n : ℕ}
    (ih : ∀ m < n, ∀ (V : Type) [Fintype V] (H : SimpleGraph V) (u v : V),
      Fintype.card V + Nat.card H.edgeSet = m → u ≠ v →
      IsPlanar (H.deleteEdges {s(u, v)}) → (H.deleteEdges {s(u, v)}).CliqueFree 3 →
      H.Colorable 3)
    (H : SimpleGraph V) {u v a c : V} (hn : Fintype.card V + Nat.card H.edgeSet = n)
    (huv : u ≠ v) (hac : a ≠ c) (hsac : s(a, c) ≠ s(u, v))
    (hnadj : ¬ (H.deleteEdges {s(u, v)}).Adj a c)
    (hP : IsPlanar (glue (H.deleteEdges {s(u, v)}) a c))
    (h3 : (glue (H.deleteEdges {s(u, v)}) a c).CliqueFree 3) : H.Colorable 3 := by
  have hadj : ¬ H.Adj a c := fun h => hnadj (pe_adj_of_ne h hsac)
  let f : V → {w // w ≠ c} := fun w => if h : w = c then ⟨a, hac⟩ else ⟨w, h⟩
  have hf : ∀ w (h : w ≠ c), f w = ⟨w, h⟩ := fun w h => by simp [f, h]
  have hfc : f c = ⟨a, hac⟩ := by simp [f]
  have hne : f u ≠ f v := by
    intro h
    by_cases hu : u = c
    · subst hu
      rw [hfc, hf v (Ne.symm huv)] at h
      have h' := congrArg Subtype.val h
      simp only at h'
      subst h'
      exact hsac Sym2.eq_swap
    by_cases hv : v = c
    · subst hv
      rw [hfc, hf u hu] at h
      have h' := congrArg Subtype.val h
      simp only at h'
      subst h'
      exact hsac rfl
    rw [hf u hu, hf v hv] at h
    exact huv (congrArg Subtype.val h)
  have hle : ∀ p q : {w // w ≠ c},
      ((glue H a c).deleteEdges {s(f u, f v)}).Adj p q →
      (glue (H.deleteEdges {s(u, v)}) a c).Adj p q := by
    intro p q hpq
    rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at hpq
    obtain ⟨⟨hpq0, hpq1⟩, hpq2⟩ := hpq
    refine ⟨hpq0, ?_⟩
    rcases hpq1 with h | ⟨h1, h⟩ | ⟨h1, h⟩
    · refine Or.inl (pe_adj_of_ne h fun he => hpq2 ?_)
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2, hf _ p.2, hf _ q.2]
      · rw [← h1, ← h2, hf _ p.2, hf _ q.2, Sym2.eq_swap]
    · refine Or.inr (Or.inl ⟨h1, pe_adj_of_ne h fun he => hpq2 ?_⟩)
      have hp : p = ⟨a, hac⟩ := Subtype.ext h1
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2, hfc, hf _ q.2, hp]
      · rw [← h1, ← h2, hfc, hf _ q.2, hp, Sym2.eq_swap]
    · refine Or.inr (Or.inr ⟨h1, pe_adj_of_ne h fun he => hpq2 ?_⟩)
      have hq : q = ⟨a, hac⟩ := Subtype.ext h1
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2, hfc, hf _ p.2, hq, Sym2.eq_swap]
      · rw [← h1, ← h2, hfc, hf _ p.2, hq]
  have hcard : Fintype.card {w // w ≠ c} < Fintype.card V :=
    Fintype.card_subtype_lt (p := fun w => w ≠ c) (x := c) (by simp)
  have hedge := card_edgeSet_glue_le (G := H) a c hac
  have hT := planar_cliqueFree_of_injective
    (X := (glue H a c).deleteEdges {s(f u, f v)}) (Y := glue (H.deleteEdges {s(u, v)}) a c)
    id Function.injective_id hle
  exact colorable_of_glue hac hadj
    (ih _ (by omega) _ (glue H a c) (f u) (f v) rfl hne (hT.1 hP) (hT.2 h3))

private lemma pe_four_le_card {M : PlaneMap G} {d₀ d₁ d₂ d₃ : G.Dart}
    (hF : FourFace M d₀ d₁ d₂ d₃) : 4 ≤ Nat.card {e // SameCycle M.facePerm d₀ e} := by
  have n01 : d₀ ≠ d₁ := fun h => hF.adj₀.ne (congrArg (fun d : G.Dart => d.fst) h)
  have n02 : d₀ ≠ d₂ := fun h => hF.ne02 (congrArg (fun d : G.Dart => d.fst) h)
  have n03 : d₀ ≠ d₃ := fun h => hF.adj₃.ne (congrArg (fun d : G.Dart => d.fst) h).symm
  have n12 : d₁ ≠ d₂ := fun h => hF.adj₁.ne (congrArg (fun d : G.Dart => d.fst) h)
  have n13 : d₁ ≠ d₃ := fun h => hF.ne13 (congrArg (fun d : G.Dart => d.fst) h)
  have n23 : d₂ ≠ d₃ := fun h => hF.adj₂.ne (congrArg (fun d : G.Dart => d.fst) h)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hS : ({d₀, d₁, d₂, d₃} : Finset G.Dart).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [n01, n02, n03]),
      Finset.card_insert_of_notMem (by simp [n12, n13]),
      Finset.card_insert_of_notMem (by simp [n23]), Finset.card_singleton]
  rw [← hS]
  apply Finset.card_le_card
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;>
    simp [SameCycle.refl, hF.same₁, hF.same₂, hF.same₃]

private lemma pe_normalize {M : PlaneMap G} {d₀ d₁ d₂ d₃ : G.Dart} {u v : V}
    (hF : FourFace M d₀ d₁ d₂ d₃)
    (h : ¬ (s(d₀.fst, d₂.fst) ≠ s(u, v) ∧ s(d₁.fst, d₃.fst) ≠ s(u, v))) :
    ∃ e₀ e₁ e₂ e₃, FourFace M e₀ e₁ e₂ e₃ ∧ SameCycle M.facePerm d₀ e₀ ∧
      e₀.fst = u ∧ e₂.fst = v := by
  rw [not_and_or, not_not, not_not] at h
  rcases h with h | h <;> rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨d₀, d₁, d₂, d₃, hF, SameCycle.refl _ _, h1, h2⟩
  · exact ⟨d₂, d₃, d₀, d₁, hF.rotate.rotate, hF.same₂, h2, h1⟩
  · exact ⟨d₁, d₂, d₃, d₀, hF.rotate, hF.same₁, h1, h2⟩
  · exact ⟨d₃, d₀, d₁, d₂, hF.rotate.rotate.rotate, hF.same₃, h2, h1⟩

omit [Fintype V] in
private lemma pe_dart_eq {d : G.Dart} {a b : V} (h : G.Adj a b) (ha : d.fst = a)
    (hb : d.snd = b) : (⟨(a, b), h⟩ : G.Dart) = d :=
  by rw [SimpleGraph.Dart.ext_iff]; exact Prod.ext ha.symm hb.symm

private lemma pe_common_corner {M : PlaneMap G} {d₀ d₁ d₂ d₃ e₀ e₁ e₂ e₃ : G.Dart}
    (hF : FourFace M d₀ d₁ d₂ d₃) (hE : FourFace M e₀ e₁ e₂ e₃)
    (h0 : d₀.fst = e₀.fst) (h2 : d₂.fst = e₂.fst) (hns : ¬ SameCycle M.facePerm d₀ e₀)
    (hdeg : ∀ z, z ≠ d₀.fst → z ≠ d₂.fst → 3 ≤ Nat.card {w // G.Adj z w}) :
    d₁.fst ≠ e₁.fst ∧ d₁.fst ≠ e₃.fst := by
  constructor
  · intro h
    apply hns
    have : d₀ = e₀ := by
      rw [SimpleGraph.Dart.ext_iff]; exact Prod.ext h0 (by rw [hF.snd₀, hE.snd₀, h])
    exact this ▸ SameCycle.refl _ _
  · intro h
    have hle := card_adj_le_two_of_opposite M hF.adj₀ hF.adj₁
      (by rw [pe_dart_eq hF.adj₀ rfl hF.snd₀, pe_dart_eq hF.adj₁ rfl hF.snd₁]; exact hF.f01)
      (by
        rw [pe_dart_eq hF.adj₁.symm h2.symm (hE.snd₂.trans h.symm),
          pe_dart_eq hF.adj₀.symm h.symm (hE.snd₃.trans h0.symm)]
        exact hE.f23)
    have := hdeg d₁.fst hF.adj₀.ne.symm hF.adj₁.ne
    omega

private lemma pe_case3 {n : ℕ}
    (ih : ∀ m < n, ∀ (V : Type) [Fintype V] (H : SimpleGraph V) (u v : V),
      Fintype.card V + Nat.card H.edgeSet = m → u ≠ v →
      IsPlanar (H.deleteEdges {s(u, v)}) → (H.deleteEdges {s(u, v)}).CliqueFree 3 →
      H.Colorable 3)
    (H : SimpleGraph V) {u v : V} (hn : Fintype.card V + Nat.card H.edgeSet = n) (huv : u ≠ v)
    (M : PlaneMap (H.deleteEdges {s(u, v)})) (h3 : (H.deleteEdges {s(u, v)}).CliqueFree 3)
    {d₀ d₁ d₂ d₃ : (H.deleteEdges {s(u, v)}).Dart} (hF : FourFace M d₀ d₁ d₂ d₃)
    (h02 : s(d₀.fst, d₂.fst) ≠ s(u, v)) (h13 : s(d₁.fst, d₃.fst) ≠ s(u, v)) :
    H.Colorable 3 := by
  have tri : ∀ p q r : V, (H.deleteEdges {s(u, v)}).Adj p q →
      (H.deleteEdges {s(u, v)}).Adj p r → (H.deleteEdges {s(u, v)}).Adj q r → False :=
    fun p q r hpq hpr hqr => h3 {p, q, r} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hpq, hpr, hqr⟩)
  have hinj := hF.inj
  obtain ⟨m0, m1, m2, m3⟩ := hF.mem_faceVerts
  have n02 : ¬ (H.deleteEdges {s(u, v)}).Adj d₀.fst d₂.fst :=
    fun h => tri _ _ _ hF.adj₀ h hF.adj₁
  have n13 : ¬ (H.deleteEdges {s(u, v)}).Adj d₁.fst d₃.fst :=
    fun h => tri _ _ _ hF.adj₁ h hF.adj₂
  by_cases hA : (glue (H.deleteEdges {s(u, v)}) d₀.fst d₂.fst).CliqueFree 3
  · exact pe_glue_step ih H hn huv hF.ne02 h02 n02 (isPlanar_glue M d₀ hinj hF.ne02 m0 m2) hA
  by_cases hB : (glue (H.deleteEdges {s(u, v)}) d₁.fst d₃.fst).CliqueFree 3
  · exact pe_glue_step ih H hn huv hF.ne13 h13 n13 (isPlanar_glue M d₀ hinj hF.ne13 m1 m3) hB
  obtain ⟨b, c, hxb, hbc, hcz, -, -⟩ := exists_path_of_not_cliqueFree_glue h3 hF.ne02 n02 hA
  obtain ⟨b', c', hyb', hb'c', hc'u, -, -⟩ :=
    exists_path_of_not_cliqueFree_glue h3 hF.ne13 n13 hB
  exact (no_crossing_paths M d₀ h3 hinj hF.adj₀ hF.adj₁ hF.adj₂ hF.adj₃ m0 m1 m2 m3
    hxb hbc hcz hyb' hb'c' hc'u).elim

private lemma pe_case2 {n : ℕ}
    (ih : ∀ m < n, ∀ (V : Type) [Fintype V] (H : SimpleGraph V) (u v : V),
      Fintype.card V + Nat.card H.edgeSet = m → u ≠ v →
      IsPlanar (H.deleteEdges {s(u, v)}) → (H.deleteEdges {s(u, v)}).CliqueFree 3 →
      H.Colorable 3)
    (H : SimpleGraph V) {u v : V} (hn : Fintype.card V + Nat.card H.edgeSet = n) (huv : u ≠ v)
    (M : PlaneMap (H.deleteEdges {s(u, v)})) (h3 : (H.deleteEdges {s(u, v)}).CliqueFree 3)
    (hdeg : ∀ z, z ≠ u → z ≠ v → 3 ≤ Nat.card {w // (H.deleteEdges {s(u, v)}).Adj z w})
    {d₀ d₁ d₂ d₃ e₀ e₁ e₂ e₃ : (H.deleteEdges {s(u, v)}).Dart}
    (hF : FourFace M d₀ d₁ d₂ d₃) (hE : FourFace M e₀ e₁ e₂ e₃)
    (hd0 : d₀.fst = u) (hd2 : d₂.fst = v) (he0 : e₀.fst = u) (he2 : e₂.fst = v)
    (hns : ¬ SameCycle M.facePerm d₀ e₀) : H.Colorable 3 := by
  have tri : ∀ p q r : V, (H.deleteEdges {s(u, v)}).Adj p q →
      (H.deleteEdges {s(u, v)}).Adj p r → (H.deleteEdges {s(u, v)}).Adj q r → False :=
    fun p q r hpq hpr hqr => h3 {p, q, r} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hpq, hpr, hqr⟩)
  have A1 : (H.deleteEdges {s(u, v)}).Adj u d₁.fst := by
    have h := hF.adj₀; rwa [hd0] at h
  have A2 : (H.deleteEdges {s(u, v)}).Adj d₁.fst v := by
    have h := hF.adj₁; rwa [hd2] at h
  have A3 : (H.deleteEdges {s(u, v)}).Adj v d₃.fst := by
    have h := hF.adj₂; rwa [hd2] at h
  have A4 : (H.deleteEdges {s(u, v)}).Adj d₃.fst u := by
    have h := hF.adj₃; rwa [hd0] at h
  have B1 : (H.deleteEdges {s(u, v)}).Adj u e₁.fst := by
    have h := hE.adj₀; rwa [he0] at h
  have B2 : (H.deleteEdges {s(u, v)}).Adj e₁.fst v := by
    have h := hE.adj₁; rwa [he2] at h
  have B3 : (H.deleteEdges {s(u, v)}).Adj v e₃.fst := by
    have h := hE.adj₂; rwa [he2] at h
  have B4 : (H.deleteEdges {s(u, v)}).Adj e₃.fst u := by
    have h := hE.adj₃; rwa [he0] at h
  have hc1 := pe_common_corner hF hE (hd0.trans he0.symm) (hd2.trans he2.symm) hns
    (fun z h1 h2 => hdeg z (hd0 ▸ h1) (hd2 ▸ h2))
  have hc2 := pe_common_corner hF.rotate.rotate hE.rotate.rotate (hd2.trans he2.symm)
    (hd0.trans he0.symm) (fun h => hns (hF.same₂.trans (h.trans hE.same₂.symm)))
    (fun z h1 h2 => hdeg z (hd0 ▸ h2) (hd2 ▸ h1))
  obtain ⟨m0, m1, m2, m3⟩ := hF.mem_faceVerts
  rw [hd0] at m0
  rw [hd2] at m2
  have n13 : ¬ (H.deleteEdges {s(u, v)}).Adj d₁.fst d₃.fst :=
    fun h => tri u _ _ A1 A4.symm h
  have hs : s(d₁.fst, d₃.fst) ≠ s(u, v) := by
    rw [Ne, Sym2.eq_iff]
    rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact A1.ne h.symm
    · exact A2.ne h
  by_cases hA : (glue (H.deleteEdges {s(u, v)}) d₁.fst d₃.fst).CliqueFree 3
  · exact pe_glue_step ih H hn huv hF.ne13 hs n13 (isPlanar_glue M d₀ hF.inj hF.ne13 m1 m3) hA
  exfalso
  obtain ⟨q₁, q₂, h1, h2, h3', hq₁x₂, -⟩ := exists_path_of_not_cliqueFree_glue h3 hF.ne13 n13 hA
  have hq : q₁ ≠ u ∧ q₁ ≠ v ∧ q₂ ≠ u ∧ q₂ ≠ v := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl
    · exact tri _ _ _ h2 A4.symm h3'
    · exact tri _ _ _ h2 A3 h3'
    · exact tri _ _ _ h1 A1.symm h2
    · exact tri _ _ _ h1 A2 h2
  have key : ∀ y, (H.deleteEdges {s(u, v)}).Adj u y → (H.deleteEdges {s(u, v)}).Adj v y →
      y ≠ d₁.fst → y ≠ d₃.fst → y = q₁ ∨ y = q₂ := by
    intro y huy hvy hy1 hy3
    by_contra hy
    rw [not_or] at hy
    exact path_through_common_neighbour M d₀ hF.inj m0 m1 m2 m3 A1 A4.symm A2.symm A3
      huy hvy h1 h2 h3' ⟨hy1, hy3, hy.1, hy.2⟩ hq hF.ne13 huv hq₁x₂
  have k1 := key _ B1 B2.symm hc1.1.symm hc2.2.symm
  have k2 := key _ B4.symm B3 hc1.2.symm hc2.1.symm
  have hy := hE.ne13
  rcases k1 with k1 | k1 <;> rcases k2 with k2 | k2
  · exact hy (k1.trans k2.symm)
  · rw [← k1, ← k2] at h2
    exact tri _ _ _ B1 B4.symm h2
  · rw [← k1, ← k2] at h2
    exact tri _ _ _ B1 B4.symm h2.symm
  · exact hy (k1.trans k2.symm)

/-! ### The theorem -/

/-- **BKLY, Theorem 2** (auxiliary form). -/
theorem colorable_of_sdiff_edge_aux : ∀ (n : ℕ) (V : Type) [Fintype V] (H : SimpleGraph V)
    (u v : V), Fintype.card V + Nat.card H.edgeSet = n → u ≠ v →
    IsPlanar (H.deleteEdges {s(u, v)}) → (H.deleteEdges {s(u, v)}).CliqueFree 3 →
    H.Colorable 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ H u v hn huv hP h3
  by_contra hcol
  have hcrit := pe_isCritical4 ih H hn huv hP h3 hcol
  have hore := five_mul_card_le H hcrit
  rw [card_edgeFinset_eq_natCard] at hore
  have hEH := pe_card_edgeSet_le H s(u, v)
  have hmin := hcrit.three_le_degree
  have hminC : ∀ w, 2 ≤ Nat.card {x // (H.deleteEdges {s(u, v)}).Adj w x} := fun w => by
    have h1 := pe_card_adj_le_succ H u v w
    rw [pe_card_adj_eq_degree H w] at h1
    have := hmin w
    omega
  have hdegG : ∀ z, z ≠ u → z ≠ v → 3 ≤ Nat.card {w // (H.deleteEdges {s(u, v)}).Adj z w} :=
    fun z hzu hzv => by
      have h1 := pe_card_adj_le H hzu hzv
      rw [pe_card_adj_eq_degree H z] at h1
      have := hmin z
      omega
  have hiso : ∀ w, ∃ x, (H.deleteEdges {s(u, v)}).Adj w x := by
    intro w
    obtain ⟨⟨x, hx⟩⟩ := (Nat.card_pos_iff (α := {x // (H.deleteEdges {s(u, v)}).Adj w x}).mp
      (by have := hminC w; omega)).1
    exact ⟨x, hx⟩
  have hdart : Nonempty (H.deleteEdges {s(u, v)}).Dart := by
    obtain ⟨x, hx⟩ := hiso u
    exact ⟨⟨(u, x), hx⟩⟩
  obtain ⟨M⟩ := hP
  have hfour : ∀ d : (H.deleteEdges {s(u, v)}).Dart,
      Nat.card {e // SameCycle M.facePerm d e} ≤ 4 → ∃ d₁ d₂ d₃, FourFace M d d₁ d₂ d₃ :=
    exists_fourFace M h3 fun w => by rw [← pe_card_adj_eq_degree]; exact hminC w
  have h4 : ∀ d : (H.deleteEdges {s(u, v)}).Dart,
      4 ≤ Nat.card {e // SameCycle M.facePerm d e} := fun d =>
    Nat.le_of_not_lt fun hlt => by
      obtain ⟨d₁, d₂, d₃, hF⟩ := hfour d (by omega)
      have := pe_four_le_card hF
      omega
  by_cases hc1 : ∀ d d' : (H.deleteEdges {s(u, v)}).Dart,
      Nat.card {e // SameCycle M.facePerm d e} = 4 →
      Nat.card {e // SameCycle M.facePerm d' e} = 4 → SameCycle M.facePerm d d'
  · have := three_mul_card_edgeSet_add_nine_le M hiso h4 hc1
    omega
  push Not at hc1
  obtain ⟨d, d', hd, hd', hns⟩ := hc1
  obtain ⟨d₁, d₂, d₃, hF⟩ := hfour d (by omega)
  obtain ⟨d₁', d₂', d₃', hF'⟩ := hfour d' (by omega)
  by_cases hA : s(d.fst, d₂.fst) ≠ s(u, v) ∧ s(d₁.fst, d₃.fst) ≠ s(u, v)
  · exact hcol (pe_case3 ih H hn huv M h3 hF hA.1 hA.2)
  by_cases hB : s(d'.fst, d₂'.fst) ≠ s(u, v) ∧ s(d₁'.fst, d₃'.fst) ≠ s(u, v)
  · exact hcol (pe_case3 ih H hn huv M h3 hF' hB.1 hB.2)
  obtain ⟨e₀, e₁, e₂, e₃, hE, hsE, he0, he2⟩ := pe_normalize hF hA
  obtain ⟨f₀, f₁, f₂, f₃, hE', hsE', hf0, hf2⟩ := pe_normalize hF' hB
  exact hcol (pe_case2 ih H hn huv M h3 hdegG hE hE' he0 he2 hf0 hf2
    (fun h => hns (hsE.trans (h.trans hsE'.symm))))

/-- **Aksenov / Jensen–Thomassen.** A graph obtained from a triangle-free planar graph by adding one
edge is 3-colourable. -/
theorem colorable_of_sdiff_edge (H : SimpleGraph V) {u v : V} (huv : u ≠ v)
    (hP : IsPlanar (H.deleteEdges {s(u, v)})) (h3 : (H.deleteEdges {s(u, v)}).CliqueFree 3) :
    H.Colorable 3 :=
  colorable_of_sdiff_edge_aux _ V H u v rfl huv hP h3

end Grotzsch
