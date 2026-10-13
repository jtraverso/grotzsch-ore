/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Grotzsch.GrunbaumAksenov

/-!
# Grünbaum–Aksenov: Cases 2 and 3, and the theorem

Continuation of `Grotzsch.GrunbaumAksenov`. Let `G` be a smallest counterexample (`GAMin G`) and
`M` a plane map of `G`; by Case 1 there is a four-face `F = v₀ v₁ v₂ v₃`.
* **Case 2** (`GAMin.not_adj_of_fourFace`): `F` has no chord. A chord `v₀ v₂` makes `v₀ v₁ v₂` a
  triangle; it does not separate `G` (`GAMin.rIn_of_clique`), so it is a face (`cycle_facial`),
  and together with `F` this forces `v₁` to have degree at most 2.
* **Lemma 10, first half** (`GAMin.exists_path_of_fourFace`): identifying `v₀` and `v₂` keeps the
  graph planar and smaller, so it must have more than three triangles; the new triangle comes from
  a path `v₀ p q v₂` with `p v₂` and `q v₀` not edges.
* **Crossing** (`no_crossing_paths_of_ne`): paths `v₀ p q v₂` and `v₁ p' q' v₃` with all eight
  vertices distinct cannot both exist (`K₅` minor with an apex inside `F`).
-/

@[expose] public section

noncomputable section

open Classical Finset Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

namespace Grotzsch

variable {V : Type} [Fintype V] {G : SimpleGraph V}

/-! ### Case 2: four-faces have no chords -/

/-- **Case 2.** In a smallest counterexample, a four-face has no chord. -/
theorem GAMin.not_adj_of_fourFace (hG : GAMin G) (M : PlaneMap G) {d₀ d₁ d₂ d₃ : G.Dart}
    (hF : FourFace M d₀ d₁ d₂ d₃) : ¬ G.Adj d₀.fst d₂.fst := by
  intro hxz
  have hxy := hF.adj₀
  have hyz := hF.adj₁
  have n1 := hxy.ne
  have n2 := hyz.ne
  have n3 := hxz.ne
  let c : ZMod 3 → V := fun i => (![d₀.fst, d₁.fst, d₂.fst] : Fin 3 → V) i
  have hcyc : IsCycleMap G c := by
    refine ⟨fun i j h => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp [c] at h; simp_all)
    · fin_cases i
      · exact hxy
      · exact hyz
      · exact hxz.symm
  have hch : IsChordless G c := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | (left; rfl) | (right; rfl) | exact (h.ne rfl).elim
  have hS : ∀ a ∈ Set.range c, ∀ b ∈ Set.range c, a ≠ b → G.Adj a b := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    fin_cases i <;> fin_cases j <;> simp [c] at hne ⊢ <;>
      first | exact hxy | exact hyz | exact hxz | exact hxy.symm | exact hyz.symm | exact hxz.symm
  rcases cycle_facial M (by norm_num) hcyc hch
    (fun d e hd he => hG.rIn_of_clique hS hd he) with h | h
  · have := h 2 d₁.symm ⟨(d₂.fst, d₀.fst), hxz.symm⟩ hF.snd₁ rfl rfl rfl
    rw [← PlaneMap.facePerm_apply, hF.f12] at this
    have h2 := hF.snd₂
    rw [this] at h2
    exact hF.adj₃.ne h2.symm
  · have h1 := h 2 d₁ d₀.symm rfl hF.snd₁ hF.snd₀ rfl
    have h2 : M.rot d₀.symm = d₁ := hF.f01
    have := card_adj_le_two_of_rot_swap M h2 h1
    rw [dart_symm_fst, hF.snd₀, card_adj_eq_degree] at this
    have := hG.isCritical4.three_le_degree d₁.fst
    omega

/-! ### Crossing paths through a four-face -/

/-- Opposite corners of a vertex-injective 4-face `x y z u` cannot both be joined by paths of
length 3 whose interior vertices are off the face and distinct: the apex inside the face and the
two paths would form a `K₅` minor of a planar graph. -/
theorem no_crossing_paths_of_ne (M : PlaneMap G) (o : G.Dart)
    (hinj : ∀ e e' : FaceApex.F M o, e.1.fst = e'.1.fst → e = e') {x y z u : V}
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hzu : G.Adj z u) (hux : G.Adj u x) (hxz : x ≠ z)
    (hyu : y ≠ u)
    (hx : x ∈ FaceApex.faceVerts M o) (hy : y ∈ FaceApex.faceVerts M o)
    (hz : z ∈ FaceApex.faceVerts M o) (hu : u ∈ FaceApex.faceVerts M o)
    {b c b' c' : V} (hxb : G.Adj x b) (hbc : G.Adj b c) (hcz : G.Adj c z)
    (hyb' : G.Adj y b') (hb'c' : G.Adj b' c') (hc'u : G.Adj c' u)
    (hb : b ≠ x ∧ b ≠ y ∧ b ≠ z ∧ b ≠ u) (hc : c ≠ x ∧ c ≠ y ∧ c ≠ z ∧ c ≠ u)
    (hb' : b' ≠ x ∧ b' ≠ y ∧ b' ≠ z ∧ b' ≠ u) (hc' : c' ≠ x ∧ c' ≠ y ∧ c' ≠ z ∧ c' ≠ u)
    (hbb' : b ≠ b') (hbc' : b ≠ c') (hcb' : c ≠ b') (hcc' : c ≠ c') : False := by
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hc
  obtain ⟨hb'1, hb'2, hb'3, hb'4⟩ := hb'
  obtain ⟨hc'1, hc'2, hc'3, hc'4⟩ := hc'
  have h1 : x ≠ b' := hb'1.symm
  have h2 : b ≠ y := hb2
  have h3' : b ≠ b' := hbb'
  have h4 : x ≠ z := hxz
  have h5 : x ≠ c := hc1.symm
  have h6 : b ≠ z := hb3
  have h7 : x ≠ c' := hc'1.symm
  have h8 : b ≠ u := hb4
  have h9 : b ≠ c' := hbc'
  have h10 : y ≠ c := hc2.symm
  have h11 : b' ≠ z := hb'3
  have h12 : b' ≠ c := hcb'.symm
  have h13 : y ≠ u := hyu
  have h14 : y ≠ c' := hc'2.symm
  have h15 : b' ≠ u := hb'4
  have h16 : z ≠ c' := hc'3.symm
  have h17 : c ≠ u := hc4
  have h18 : c ≠ c' := hcc'
  clear hb1 hb2 hb3 hb4 hc1 hc2 hc3 hc4 hb'1 hb'2 hb'3 hb'4 hc'1 hc'2 hc'3 hc'4 hbb' hbc' hcb' hcc'
    hxz hyu
  have hxy' := hxy.ne
  have hyz' := hyz.ne
  have hzu' := hzu.ne
  have hux' := hux.ne
  have s1 := h1.symm; have s2 := h2.symm; have s3 := h3'.symm; have s4 := h4.symm
  have s5 := h5.symm; have s6 := h6.symm; have s7 := h7.symm; have s8 := h8.symm
  have s9 := h9.symm; have s10 := h10.symm; have s11 := h11.symm; have s12 := h12.symm
  have s13 := h13.symm; have s14 := h14.symm; have s15 := h15.symm; have s16 := h16.symm
  have s17 := h17.symm; have s18 := h18.symm; have sxy := hxy'.symm; have syz := hyz'.symm
  have szu := hzu'.symm; have sux := hux'.symm
  have hbc' := hbc.ne; have sbc := hbc.ne.symm; have hbc'' := hb'c'.ne; have sbc' := hb'c'.ne.symm
  -- the apex graph and its `K₅` minor
  set A := apexExtend G (FaceApex.faceVerts M o)
  have hP := isPlanar_apexExtend_face M o hinj
  have conn2 : ∀ p q : V, G.Adj p q →
      (A.induce (↑({some p, some q} : Finset (Option V)) : Set (Option V))).Connected := by
    intro p q hpq
    rw [← connSet_iff_induce_connected]
    have := (connSet_singleton A (some q)).insert_adj (a := some p) (Set.mem_singleton _) hpq
    simpa using this
  let br : Fin 5 → Finset (Option V) :=
    ![{none}, {some x, some b}, {some y, some b'}, {some z, some c}, {some u, some c'}]
  refine cliqueMinorFree_five_of_isPlanar hP ⟨{
    branch := br
    branch_nonempty := fun i => by fin_cases i <;> simp [br]
    branch_connected := fun i => ?_
    branch_disjoint := fun i j hij => ?_
    branch_adjacent := fun i j hij => ?_ }⟩
  · fin_cases i
    · rw [← connSet_iff_induce_connected]; simpa [br] using connSet_singleton A none
    · exact conn2 x b hxb
    · exact conn2 y b' hyb'
    · exact conn2 z c hcz.symm
    · exact conn2 u c' hc'u.symm
  · rw [Finset.disjoint_left]
    fin_cases i <;> fin_cases j <;> simp_all [br]
  · have key : ∀ i j : Fin 5, i < j → ∃ p ∈ br i, ∃ q ∈ br j, A.Adj p q := by
      intro i j hlt
      fin_cases i <;> fin_cases j <;> first | (exfalso; revert hlt; decide) | skip
      · exact ⟨none, by simp [br], some x, by simp [br], hx⟩
      · exact ⟨none, by simp [br], some y, by simp [br], hy⟩
      · exact ⟨none, by simp [br], some z, by simp [br], hz⟩
      · exact ⟨none, by simp [br], some u, by simp [br], hu⟩
      · exact ⟨some x, by simp [br], some y, by simp [br], hxy⟩
      · exact ⟨some b, by simp [br], some c, by simp [br], hbc⟩
      · exact ⟨some x, by simp [br], some u, by simp [br], hux.symm⟩
      · exact ⟨some y, by simp [br], some z, by simp [br], hyz⟩
      · exact ⟨some b', by simp [br], some c', by simp [br], hb'c'⟩
      · exact ⟨some z, by simp [br], some u, by simp [br], hzu⟩
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · obtain ⟨p, hp, q, hq, hpq⟩ := key j i h
      exact ⟨q, hq, p, hp, hpq.symm⟩

/-! ### Lemma 10, first half -/

omit [Fintype V] in
private theorem glue_adj_plain {x z : V} {p q : {v // v ≠ z}} (hp : p.1 ≠ x) (hq : q.1 ≠ x)
    (h : (glue G x z).Adj p q) : G.Adj p q := by
  rcases h.2 with h' | h' | h'
  · exact h'
  · exact absurd h'.1 hp
  · exact absurd h'.1 hq

omit [Fintype V] in
private theorem glue_adj_fromx {x z : V} {p q : {v // v ≠ z}} (hp : p.1 = x) (hq : q.1 ≠ x)
    (h : (glue G x z).Adj p q) : G.Adj x q ∨ G.Adj z q := by
  rcases h.2 with h' | h' | h'
  · exact Or.inl (hp ▸ h')
  · exact Or.inr h'.2
  · exact absurd h'.1 hq

omit [Fintype V] in
private theorem glue_map_triple {z : V} (a b c : {v // v ≠ z}) :
    ({a, b, c} : Finset {v // v ≠ z}).map (Function.Embedding.subtype _) = {a.1, b.1, c.1} := by
  simp

omit [Fintype V] in
private theorem glue_tri_plain {x z : V} {t : Finset {v // v ≠ z}}
    (ht : (glue G x z).IsNClique 3 t) (hx : x ∉ t.map (Function.Embedding.subtype _)) :
    G.IsNClique 3 (t.map (Function.Embedding.subtype _)) := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := SimpleGraph.is3Clique_iff.mp ht
  rw [glue_map_triple] at hx ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  obtain ⟨ha, hb, hc⟩ := hx
  exact SimpleGraph.is3Clique_triple_iff.mpr ⟨glue_adj_plain (Ne.symm ha) (Ne.symm hb) hab,
    glue_adj_plain (Ne.symm ha) (Ne.symm hc) hac, glue_adj_plain (Ne.symm hb) (Ne.symm hc) hbc⟩

omit [Fintype V] in
private theorem glue_tri_main {x z : V}
    (H : ∀ p q, G.Adj x p → G.Adj p q → G.Adj q z → ¬ G.Adj p z → G.Adj q x)
    {p q r : {v // v ≠ z}} (hp : p.1 = x) (hq : q.1 ≠ x) (hr : r.1 ≠ x)
    (hpq : (glue G x z).Adj p q) (hpr : (glue G x z).Adj p r) (hqr : (glue G x z).Adj q r)
    (hn : ¬ G.IsNClique 3 ({x, q.1, r.1} : Finset V)) :
    G.IsNClique 3 ({z, q.1, r.1} : Finset V) := by
  have hqr' := glue_adj_plain hq hr hqr
  have zcase : G.Adj z q → G.Adj z r → G.IsNClique 3 ({z, q.1, r.1} : Finset V) :=
    fun h1 h2 => SimpleGraph.is3Clique_triple_iff.mpr ⟨h1, h2, hqr'⟩
  have xcase : G.Adj x q → G.Adj x r → False :=
    fun h1 h2 => hn (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1, h2, hqr'⟩)
  rcases glue_adj_fromx hp hq hpq with h1 | h1 <;>
    rcases glue_adj_fromx hp hr hpr with h2 | h2
  · exact (xcase h1 h2).elim
  · by_cases h3 : G.Adj q z
    · exact zcase h3.symm h2
    · exact (xcase h1 (H q r h1 hqr' h2.symm h3).symm).elim
  · by_cases h3 : G.Adj r z
    · exact zcase h1 h3.symm
    · exact (xcase (H r q h2 hqr'.symm h1.symm h3).symm h2).elim
  · exact zcase h1 h2

omit [Fintype V] in
private theorem glue_tri_z {x z : V}
    (H : ∀ p q, G.Adj x p → G.Adj p q → G.Adj q z → ¬ G.Adj p z → G.Adj q x)
    {t : Finset {v // v ≠ z}} (ht : (glue G x z).IsNClique 3 t)
    (hn : ¬ G.IsNClique 3 (t.map (Function.Embedding.subtype _))) :
    G.IsNClique 3 (insert z ((t.map (Function.Embedding.subtype _)).erase x)) := by
  have hx : x ∈ t.map (Function.Embedding.subtype _) := by
    by_contra hx
    exact hn (glue_tri_plain ht hx)
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := SimpleGraph.is3Clique_iff.mp ht
  rw [glue_map_triple] at hx hn ⊢
  have hab' : a.1 ≠ b.1 := fun h => hab.1 (Subtype.ext h)
  have hac' : a.1 ≠ c.1 := fun h => hac.1 (Subtype.ext h)
  have hbc' : b.1 ≠ c.1 := fun h => hbc.1 (Subtype.ext h)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with ha | hb | hc
  · subst ha
    rw [Finset.erase_insert (by simp [hab', hac'])]
    exact glue_tri_main H rfl (Ne.symm hab') (Ne.symm hac') hab hac hbc hn
  · subst hb
    have e : ({a.1, b.1, c.1} : Finset V) = {b.1, a.1, c.1} := Finset.insert_comm _ _ _
    rw [e] at hn ⊢
    rw [Finset.erase_insert (by simp [Ne.symm hab', hbc'])]
    exact glue_tri_main H rfl hab' (Ne.symm hbc') hab.symm hbc hac hn
  · subst hc
    have e : ({a.1, b.1, c.1} : Finset V) = {c.1, a.1, b.1} := by
      ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [e] at hn ⊢
    rw [Finset.erase_insert (by simp [Ne.symm hac', Ne.symm hbc'])]
    exact glue_tri_main H rfl hac' hbc' hac.symm hbc.symm hab hn

private theorem triCount_glue_le {x z : V}
    (H : ∀ p q, G.Adj x p → G.Adj p q → G.Adj q z → ¬ G.Adj p z → G.Adj q x) :
    triCount (glue G x z) ≤ triCount G := by
  let emb : {v // v ≠ z} ↪ V := Function.Embedding.subtype _
  let g : Finset {v // v ≠ z} → Finset V := fun t =>
    if G.IsNClique 3 (t.map emb) then t.map emb else insert z ((t.map emb).erase x)
  have hg : ∀ t, (glue G x z).IsNClique 3 t → G.IsNClique 3 (g t) := by
    intro t ht
    by_cases h : G.IsNClique 3 (t.map emb)
    · simp only [g, h, ↓reduceIte]
    · simp only [g, h, ↓reduceIte]; exact glue_tri_z H ht h
  have hzt : ∀ t : Finset {v // v ≠ z}, z ∉ t.map emb := fun t h => by
    obtain ⟨w, -, hw⟩ := Finset.mem_map.mp h
    exact w.2 hw
  have hxt : ∀ t : Finset {v // v ≠ z}, (glue G x z).IsNClique 3 t →
      ¬ G.IsNClique 3 (t.map emb) → x ∈ t.map emb := fun t ht hn => by
    by_contra hx
    exact hn (glue_tri_plain ht hx)
  refine Nat.card_le_card_of_injective (fun t => ⟨g t.1, hg t.1 t.2⟩) ?_
  rintro ⟨t, ht⟩ ⟨t', ht'⟩ h
  have h' : g t = g t' := congrArg Subtype.val h
  apply Subtype.ext
  show t = t'
  apply Finset.map_injective emb
  by_cases h1 : G.IsNClique 3 (t.map emb) <;> by_cases h2 : G.IsNClique 3 (t'.map emb) <;>
    simp only [g, h1, h2, ↓reduceIte] at h'
  · exact h'
  · exact absurd (h' ▸ Finset.mem_insert_self _ _) (hzt t)
  · exact absurd (h'.symm ▸ Finset.mem_insert_self _ _) (hzt t')
  · have hz1 : z ∉ (t.map emb).erase x := fun hm => hzt t (Finset.mem_of_mem_erase hm)
    have hz2 : z ∉ (t'.map emb).erase x := fun hm => hzt t' (Finset.mem_of_mem_erase hm)
    have e : (t.map emb).erase x = (t'.map emb).erase x := by
      rw [← Finset.erase_insert hz1, h', Finset.erase_insert hz2]
    rw [← Finset.insert_erase (hxt t ht h1), ← Finset.insert_erase (hxt t' ht' h2), e]

/-- **Identification of opposite corners.** In a smallest counterexample, identifying the
opposite corners `v₀`, `v₂` of a four-face gives a smaller planar graph, so it has at least four
triangles; a triangle not coming from `G` is a path `v₀ p q v₂` with `p v₂` and `q v₀` not edges.
-/
theorem GAMin.exists_path_of_fourFace (hG : GAMin G) (M : PlaneMap G) {d₀ d₁ d₂ d₃ : G.Dart}
    (hF : FourFace M d₀ d₁ d₂ d₃) :
    ∃ p q, G.Adj d₀.fst p ∧ G.Adj p q ∧ G.Adj q d₂.fst ∧ ¬ G.Adj p d₂.fst ∧
      ¬ G.Adj q d₀.fst := by
  have hxz := hF.ne02
  have hnadj := hG.not_adj_of_fourFace M hF
  by_contra hcon
  have H : ∀ p q, G.Adj d₀.fst p → G.Adj p q → G.Adj q d₂.fst → ¬ G.Adj p d₂.fst →
      G.Adj q d₀.fst := by
    intro p q h1 h2 h3 h4
    by_contra h5
    exact hcon ⟨p, q, h1, h2, h3, h4, h5⟩
  apply hG.not_colorable
  apply colorable_of_glue hxz hnadj
  refine hG.small {v // v ≠ d₂.fst} (glue G d₀.fst d₂.fst) ?_ ?_ ?_
  · have h1 : Fintype.card {v // v ≠ d₂.fst} < Fintype.card V :=
      Fintype.card_subtype_lt (p := (· ≠ d₂.fst)) (x := d₂.fst) (by simp)
    have h2 := card_edgeSet_glue_le (G := G) d₀.fst d₂.fst hxz
    omega
  · exact isPlanar_glue M d₀ hF.inj hxz hF.mem_faceVerts.1 hF.mem_faceVerts.2.2.1
  · exact (triCount_glue_le H).trans hG.tri

end Grotzsch
