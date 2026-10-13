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

/-! ### The theorem -/

/-- **BKLY, Theorem 2** (auxiliary form). -/
theorem colorable_of_sdiff_edge_aux : ∀ (n : ℕ) (V : Type) [Fintype V] (H : SimpleGraph V)
    (u v : V), Fintype.card V + Nat.card H.edgeSet = n → u ≠ v →
    IsPlanar (H.deleteEdges {s(u, v)}) → (H.deleteEdges {s(u, v)}).CliqueFree 3 →
    H.Colorable 3 := by
  sorry

/-- **Aksenov / Jensen–Thomassen.** A graph obtained from a triangle-free planar graph by adding one
edge is 3-colourable. -/
theorem colorable_of_sdiff_edge (H : SimpleGraph V) {u v : V} (huv : u ≠ v)
    (hP : IsPlanar (H.deleteEdges {s(u, v)})) (h3 : (H.deleteEdges {s(u, v)}).CliqueFree 3) :
    H.Colorable 3 :=
  colorable_of_sdiff_edge_aux _ V H u v rfl huv hP h3

end Grotzsch
