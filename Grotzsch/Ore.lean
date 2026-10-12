/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Option
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

/-!
# Ore's conjecture for `k = 4` (Kostochka–Yancey)

**Theorem (Kostochka–Yancey 2014).** Every 4-critical graph `G` satisfies
`3 |E(G)| ≥ 5 |V(G)| - 2`.

Reference: A. Kostochka, M. Yancey, *Ore's conjecture for k = 4 and Grötzsch's theorem*,
Combinatorica 34 (2014) 323–329, arXiv:1209.1173.

The proof uses the *potential* `ρ_G(R) = 5|R| - 3 e(G[R])` and considers a vertex-minimal
4-critical graph `G` with `ρ_G(V) > 2` (`MinCounter`). Minimality gives (3): every graph with fewer
vertices that is not 3-colourable has a vertex set of potential `≤ 2` spanning a non-3-colourable
subgraph (`SmallCritical`); in particular graphs with all potentials `> 2` are 3-colourable
(`SmallColorable`). Claims 9–13 of the paper restrict the local structure of `G`, and a
discharging argument then gives `3 |E| ≥ 5 |V|`, a contradiction.
-/

@[expose] public section

noncomputable section

open Classical Finset

namespace Grotzsch

/-- Number of edges of `G` with both ends in `R`. -/
def eIn {V : Type*} [Fintype V] (G : SimpleGraph V) (R : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ R).card

/-- The potential `ρ_G(R) = 5 |R| - 3 e(G[R])`. -/
def pot {V : Type*} [Fintype V] (G : SimpleGraph V) (R : Finset V) : ℤ :=
  5 * (R.card : ℤ) - 3 * (eIn G R : ℤ)

/-- `G` is 4-critical: not 3-colourable, but deleting any vertex or any edge makes it
3-colourable. -/
structure IsCritical4 {V : Type*} (G : SimpleGraph V) : Prop where
  not_colorable : ¬ G.Colorable 3
  vertex : ∀ v, (G.induce {w | w ≠ v}).Colorable 3
  edge : ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).Colorable 3

/-- Hypothesis (3) of Kostochka–Yancey: every graph on fewer than `N` vertices whose nonempty
vertex sets all have potential `> 2` is 3-colourable. -/
def SmallColorable (N : ℕ) : Prop :=
  ∀ (W : Type) [Fintype W] (H : SimpleGraph W), Fintype.card W < N →
    (∀ R : Finset W, R.Nonempty → 2 < pot H R) → H.Colorable 3

/-- Strong form of hypothesis (3): every graph on fewer than `N` vertices that is not
3-colourable has a nonempty vertex set `S` of potential `≤ 2` whose induced subgraph is still not
3-colourable (the vertex set of a 4-critical subgraph). -/
def SmallCritical (N : ℕ) : Prop :=
  ∀ (W : Type) [Fintype W] (H : SimpleGraph W), Fintype.card W < N → ¬ H.Colorable 3 →
    ∃ S : Finset W, S.Nonempty ∧ pot H S ≤ 2 ∧ ¬ (H.induce (S : Set W)).Colorable 3

/-- A minimal counterexample to the Kostochka–Yancey bound. -/
structure MinCounter {V : Type} [Fintype V] (G : SimpleGraph V) : Prop where
  crit : IsCritical4 G
  big : 2 < pot G univ
  small : SmallCritical (Fintype.card V)

/-! ### General facts -/

/-- Every finite graph that is not 3-colourable contains a 4-critical subgraph (on a subset of
the vertices). -/
theorem exists_critical_subgraph {W : Type} [Fintype W] (H : SimpleGraph W)
    (h : ¬ H.Colorable 3) :
    ∃ (S : Finset W) (H' : SimpleGraph S), (∀ a b, H'.Adj a b → H.Adj a b) ∧ IsCritical4 H' := by
  have hex : ∃ n, ∃ (S : Finset W) (H' : SimpleGraph S), (∀ a b, H'.Adj a b → H.Adj a b) ∧
      ¬ H'.Colorable 3 ∧ S.card + H'.edgeSet.ncard = n := by
    refine ⟨_, univ, H.comap Subtype.val, fun a b h => h, ?_, rfl⟩
    rintro ⟨c⟩
    exact h ⟨SimpleGraph.Coloring.mk (fun v => c ⟨v, mem_univ v⟩) (fun {a b} hab => c.valid hab)⟩
  obtain ⟨S, H', hsub, hnc, hn⟩ := Nat.find_spec hex
  have hmin : ∀ (S2 : Finset W) (H2 : SimpleGraph S2), (∀ a b, H2.Adj a b → H.Adj a b) →
      S2.card + H2.edgeSet.ncard < S.card + H'.edgeSet.ncard → H2.Colorable 3 := by
    intro S2 H2 hs hlt
    by_contra hc
    exact Nat.find_min hex (hn ▸ hlt) ⟨S2, H2, hs, hc, rfl⟩
  refine ⟨S, H', hsub, hnc, ?_, ?_⟩
  · intro v
    let f : (S.erase v.1) → S := fun w => ⟨w.1, mem_of_mem_erase w.2⟩
    have hf : Function.Injective f := fun a b hab =>
      Subtype.ext (congrArg Subtype.val hab :)
    have hlt : (S.erase v.1).card + (H'.comap f).edgeSet.ncard <
        S.card + H'.edgeSet.ncard := by
      have h1 := card_erase_of_mem v.2
      have h2 : 0 < S.card := card_pos.2 ⟨v.1, v.2⟩
      have h3 : (H'.comap f).edgeSet.ncard ≤ H'.edgeSet.ncard := by
        apply Set.ncard_le_ncard_of_injOn (Sym2.map f)
        · intro e he
          induction e using Sym2.ind with
          | _ a b => exact he
        · exact (Sym2.map.injective hf).injOn
      omega
    obtain ⟨c⟩ := hmin _ (H'.comap f) (fun a b hab => hsub _ _ hab) hlt
    exact ⟨SimpleGraph.Coloring.mk
      (fun w => c ⟨w.1.1, mem_erase.2 ⟨fun h => w.2 (Subtype.ext h), w.1.2⟩⟩)
      (fun {a b} hab => c.valid hab)⟩
  · intro e he
    apply hmin S (H'.deleteEdges {e})
      (fun a b hab => hsub a b (SimpleGraph.deleteEdges_adj.1 hab).1)
    have : (H'.deleteEdges {e}).edgeSet.ncard < H'.edgeSet.ncard := by
      apply Set.ncard_lt_ncard _ (Set.toFinite _)
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact Set.sdiff_singleton_ssubset.2 he
    omega

/-- In a 4-critical graph every vertex has degree at least 3. -/
theorem IsCritical4.three_le_degree {V : Type} [Fintype V] {G : SimpleGraph V}
    (h : IsCritical4 G) (v : V) : 3 ≤ G.degree v := by
  by_contra hlt
  push Not at hlt
  obtain ⟨c⟩ := h.vertex v
  set S : Finset (Fin 3) :=
    (G.neighborFinset v).image fun w => if hw : w = v then 0 else c ⟨w, hw⟩ with hS
  have hcard : S.card < (univ : Finset (Fin 3)).card := by
    calc S.card ≤ (G.neighborFinset v).card := card_image_le
      _ = G.degree v := SimpleGraph.card_neighborFinset_eq_degree G v
      _ < 3 := hlt
      _ = _ := by simp
  obtain ⟨a, -, ha⟩ := exists_mem_notMem_of_card_lt_card hcard
  apply h.not_colorable
  refine ⟨SimpleGraph.Coloring.mk (fun w => if hw : w = v then a else c ⟨w, hw⟩) ?_⟩
  intro x y hxy
  by_cases hx : x = v <;> by_cases hy : y = v
  · subst hx; subst hy; exact absurd hxy G.irrefl
  · subst hx
    simp only [hy, ↓reduceDIte]
    intro hc
    apply ha
    rw [hS, mem_image]
    exact ⟨y, (SimpleGraph.mem_neighborFinset _ _ _).2 hxy, by simp [hy, hc]⟩
  · subst hy
    simp only [hx, ↓reduceDIte]
    intro hc
    apply ha
    rw [hS, mem_image]
    exact ⟨x, (SimpleGraph.mem_neighborFinset _ _ _).2 hxy.symm, by simp [hx, hc]⟩
  · simp only [hx, hy, ↓reduceDIte]
    exact c.valid (by simpa using hxy)

/-- Minimality of the counterexample gives the strong form of hypothesis (3). -/
theorem smallCritical_of_minimal (N : ℕ)
    (ih : ∀ (W : Type) [Fintype W] (H : SimpleGraph W), Fintype.card W < N →
      IsCritical4 H → pot H univ ≤ 2) :
    SmallCritical N := by
  intro W _ H hW hcol
  obtain ⟨S, H', hsub, hcrit⟩ := exists_critical_subgraph H hcol
  have hS : Fintype.card S < N :=
    lt_of_le_of_lt (by rw [Fintype.card_coe]; exact card_le_univ S) hW
  have hpot := ih S H' hS hcrit
  have hle : eIn H' univ ≤ eIn H S := by
    have hE' : eIn H' univ = #H'.edgeFinset := by
      unfold eIn; congr 1; ext e; simp
    rw [hE']
    unfold eIn
    apply card_le_card_of_injOn (Sym2.map Subtype.val)
    · intro e he
      induction e using Sym2.ind with
      | _ a b =>
      simp only [coe_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        mem_coe] at he ⊢
      refine ⟨hsub a b he, ?_⟩
      intro v hv
      rw [Sym2.mem_map] at hv
      obtain ⟨u, -, rfl⟩ := hv
      exact u.2
    · intro e1 _ e2 _ h
      exact Sym2.map.injective Subtype.val_injective h
  refine ⟨S, ?_, ?_, ?_⟩
  · by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    subst hne
    apply hcrit.not_colorable
    exact ⟨SimpleGraph.Coloring.mk (fun v => (notMem_empty v.1 v.2).elim)
      (fun {v} => (notMem_empty v.1 v.2).elim)⟩
  · unfold pot at hpot ⊢
    rw [card_univ, Fintype.card_coe] at hpot
    omega
  · rintro ⟨c⟩
    apply hcrit.not_colorable
    exact ⟨SimpleGraph.Coloring.mk (fun v => c ⟨v.1, v.2⟩)
      (fun {a b} h => c.valid (by simpa using hsub a b h))⟩

/-- Hypothesis (3): graphs on fewer vertices whose nonempty sets all have potential `> 2` are
3-colourable. -/
theorem SmallCritical.smallColorable {N : ℕ} (h : SmallCritical N) : SmallColorable N := by
  intro W _ H hW hpot
  by_contra hcol
  obtain ⟨S, hS, hpotS, -⟩ := h W H hW hcol
  have := hpot S hS
  omega

/-! ### Claims 9–13 for a minimal counterexample -/

section Claims

variable {V : Type} [Fintype V] {G : SimpleGraph V}

/-- **Claim 9.** Every proper subset `R` with `|R| ≥ 2` has potential at least `6`. -/
theorem MinCounter.claim9 (hG : MinCounter G) (R : Finset V) (hR : R ≠ univ)
    (h2 : 2 ≤ R.card) : 6 ≤ pot G R := by
  sorry

/-- **Claim 10.** A proper subset `R` with `|R| ≥ 2` and potential `≤ 6` spans a triangle. -/
theorem MinCounter.claim10 (hG : MinCounter G) (R : Finset V) (hR : R ≠ univ)
    (h2 : 2 ≤ R.card) (h6 : pot G R ≤ 6) : R.card = 3 ∧ eIn G R = 3 := by
  sorry

/-- **Claim 11.** `G` contains no `K₄ - e`: four vertices span at most four edges. -/
theorem MinCounter.claim11 (hG : MinCounter G) (R : Finset V) (h4 : R.card = 4) :
    eIn G R ≤ 4 := by
  by_contra hlt
  push Not at hlt
  by_cases hR : R = univ
  · subst hR
    have hcard : Fintype.card V = 4 := by rw [← card_univ]; exact h4
    have hE : eIn G univ = #G.edgeFinset := by
      unfold eIn; congr 1; exact filter_true_of_mem fun e _ v _ => mem_univ v
    have hbig := hG.big
    rw [pot, hE, h4] at hbig
    rw [hE] at hlt
    have key : ∀ (H : SimpleGraph V) [Fintype H.edgeSet], H = ⊤ → #H.edgeFinset = 6 := by
      intro H _ hH
      subst hH
      have := SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := V)
      rw [hcard] at this
      convert this using 2
      · exact Finset.ext fun e => by simp only [SimpleGraph.mem_edgeFinset]
      · decide
    have hne : G ≠ ⊤ := fun h => by
      have := key G h
      omega
    obtain ⟨x, y, hxy, hnadj⟩ : ∃ x y, x ≠ y ∧ ¬ G.Adj x y := by
      by_contra h
      push Not at h
      apply hne
      ext a b
      simp only [SimpleGraph.top_adj]
      exact ⟨G.ne_of_adj, h a b⟩
    apply hG.crit.not_colorable
    set T := (univ.erase x).erase y with hTdef
    have hT : Fintype.card T = 2 := by
      rw [Fintype.card_coe, hTdef, card_erase_of_mem (by simp [hxy.symm]),
        card_erase_of_mem (mem_univ _), card_univ, hcard]
    let e := Fintype.equivFinOfCardEq hT
    refine ⟨SimpleGraph.Coloring.mk
      (fun v => if h : v ∈ T then (e ⟨v, h⟩).succ else (0 : Fin 3)) ?_⟩
    intro v w hvw
    by_cases hv : v ∈ T <;> by_cases hw : w ∈ T
    · simp only [hv, hw, ↓reduceDIte]
      intro h
      have h' := e.injective (Fin.succ_injective _ h)
      simp only [Subtype.mk.injEq] at h'
      exact G.ne_of_adj hvw h'
    · simp only [hv, hw, ↓reduceDIte]
      exact Fin.succ_ne_zero _
    · simp only [hv, hw, ↓reduceDIte]
      exact (Fin.succ_ne_zero _).symm
    · exfalso
      simp only [hTdef, mem_erase, mem_univ, and_true, not_and, not_not] at hv hw
      have hvw' := G.ne_of_adj hvw
      by_cases hvy : v = y <;> by_cases hwy : w = y
      · exact hvw' (hvy.trans hwy.symm)
      · have := hw hwy
        subst hvy; subst this; exact hnadj hvw.symm
      · have := hv hvy
        subst hwy; subst this; exact hnadj hvw
      · exact hvw' ((hv hvy).trans (hw hwy).symm)
  · have := hG.claim10 R hR (by omega) (by unfold pot; rw [h4]; push_cast; omega)
    omega

/-- **Claim 12.** Each triangle contains at most one vertex of degree 3. -/
theorem MinCounter.claim12 (hG : MinCounter G) {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hxz : G.Adj x z) (hx : G.degree x = 3) (hy : G.degree y = 3) : False := by
  sorry

/-- **Claim 13.** If `xy` is an edge with `d(x) = d(y) = 3`, then `x` lies in a triangle. -/
theorem MinCounter.claim13 (hG : MinCounter G) {x y : V} (hxy : G.Adj x y)
    (hx : G.degree x = 3) (hy : G.degree y = 3) :
    ∃ a b, G.Adj x a ∧ G.Adj x b ∧ G.Adj a b := by
  sorry

/-- (5): every vertex of degree 3 has at most one neighbour of degree 3. -/
theorem MinCounter.deg3_nbrs (hG : MinCounter G) (x : V) (hx : G.degree x = 3) :
    ((G.neighborFinset x).filter fun y => G.degree y = 3).card ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨y1, hy1, y2, hy2, hne⟩ := one_lt_card.1 hlt
  rw [mem_filter, SimpleGraph.mem_neighborFinset] at hy1 hy2
  obtain ⟨a, b, hxa, hxb, hab⟩ := hG.claim13 hy1.1 hx hy1.2
  have ha : G.degree a ≠ 3 := fun ha => hG.claim12 hxa hab hxb hx ha
  have hb : G.degree b ≠ 3 := fun hb => hG.claim12 hxb hab.symm hxa hx hb
  have hsub : ({a, b, y1, y2} : Finset V) ⊆ G.neighborFinset x := by
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rw [SimpleGraph.mem_neighborFinset]
    rcases hw with rfl | rfl | rfl | rfl
    exacts [hxa, hxb, hy1.1, hy2.1]
  have h4 : ({a, b, y1, y2} : Finset V).card = 4 := by
    have hab' : a ≠ b := G.ne_of_adj hab
    have h1 : a ≠ y1 := fun h => ha (h ▸ hy1.2)
    have h2 : a ≠ y2 := fun h => ha (h ▸ hy2.2)
    have h3 : b ≠ y1 := fun h => hb (h ▸ hy1.2)
    have h4 : b ≠ y2 := fun h => hb (h ▸ hy2.2)
    rw [card_insert_of_notMem (by simp [hab', h1, h2]),
      card_insert_of_notMem (by simp [h3, h4]), card_pair hne]
  have := card_le_card hsub
  rw [h4, SimpleGraph.card_neighborFinset_eq_degree, hx] at this
  omega

end Claims

private lemma t1_sum_degrees {V : Type} [Fintype V] (G : SimpleGraph V) :
    ∑ v, G.degree v = 2 * #G.edgeFinset := by
  set D := (univ : Finset (V × V)).filter fun p => G.Adj p.1 p.2
  have h1 : #D = ∑ v, G.degree v := by
    rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (by simp)]
    refine sum_congr rfl fun v _ => ?_
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have : ({a ∈ D | a.1 = v}) = (G.neighborFinset v).map
        ⟨fun w => (v, w), fun a b h => by simpa using h⟩ := by
      ext ⟨a, b⟩
      simp only [D, mem_filter, mem_univ, true_and, mem_map, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨h, rfl⟩; exact ⟨b, h, rfl⟩
      · rintro ⟨c, h, h'⟩
        change (v, c) = (a, b) at h'
        simp only [Prod.mk.injEq] at h'
        obtain ⟨rfl, rfl⟩ := h'
        exact ⟨h, rfl⟩
    rw [this, card_map]
  have h2 : #D = ∑ e ∈ G.edgeFinset, 2 := by
    rw [card_eq_sum_card_fiberwise (f := fun p => s(p.1, p.2)) (t := G.edgeFinset)]
    · refine sum_congr rfl fun e he => ?_
      induction e using Sym2.ind with
      | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have : ({x ∈ D | s(x.1, x.2) = s(a, b)}) = {(a, b), (b, a)} := by
        ext ⟨x, y⟩
        simp only [D, mem_filter, mem_univ, true_and, Sym2.eq_iff, mem_insert, mem_singleton,
          Prod.mk.injEq]
        constructor
        · rintro ⟨-, h⟩; exact h
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact ⟨he, Or.inl ⟨rfl, rfl⟩⟩
          · exact ⟨he.symm, Or.inr ⟨rfl, rfl⟩⟩
      rw [this, card_pair]
      intro h
      simp only [Prod.mk.injEq] at h
      exact G.ne_of_adj he h.1
    · intro p hp
      simp only [D, coe_filter, mem_univ, true_and] at hp
      simpa using hp
  rw [← h1, h2, sum_const_nat (fun _ _ => rfl), mul_comm]

/-- **Discharging.** If every degree is at least 3 and every vertex of degree 3 has at most one
neighbour of degree 3, then `3 |E| ≥ 5 |V|`. -/
theorem discharging {V : Type} [Fintype V] (G : SimpleGraph V) (h3 : ∀ v, 3 ≤ G.degree v)
    (h5 : ∀ x, G.degree x = 3 → ((G.neighborFinset x).filter fun y => G.degree y = 3).card ≤ 1) :
    5 * Fintype.card V ≤ 3 * G.edgeFinset.card := by
  set g : V → V → ℕ := fun v w =>
    if G.Adj v w ∧ 4 ≤ G.degree v ∧ G.degree w = 3 then 1 else 0 with hg
  have hA : ∀ v, ∑ w, g v w ≤ if 4 ≤ G.degree v then G.degree v else 0 := by
    intro v
    rw [hg]
    simp only
    rw [← card_filter]
    split_ifs with h4
    · rw [← SimpleGraph.card_neighborFinset_eq_degree]
      apply card_le_card
      intro w hw
      simp only [mem_filter] at hw
      exact (SimpleGraph.mem_neighborFinset _ _ _).2 hw.2.1
    · simp [h4]
  have hB : ∀ w, (if G.degree w = 3 then 2 else 0) ≤ ∑ v, g v w := by
    intro w
    split_ifs with hw
    · rw [hg]
      simp only
      rw [← card_filter]
      have hsplit := card_filter_add_card_filter_not
        (s := G.neighborFinset w) (fun y => G.degree y = 3)
      rw [SimpleGraph.card_neighborFinset_eq_degree, hw] at hsplit
      have h1 := h5 w hw
      have hsub : ((G.neighborFinset w).filter fun y => ¬ G.degree y = 3) ⊆
          univ.filter fun v => G.Adj v w ∧ 4 ≤ G.degree v ∧ G.degree w = 3 := by
        intro y hy
        simp only [mem_filter, SimpleGraph.mem_neighborFinset] at hy
        simp only [mem_filter, mem_univ, true_and]
        have := h3 y
        exact ⟨hy.1.symm, by omega, hw⟩
      have := card_le_card hsub
      omega
    · exact Nat.zero_le _
  have hv : ∀ v, 20 + ∑ w, g v w ≤ 6 * G.degree v + ∑ u, g u v := by
    intro v
    have a := hA v
    have b := hB v
    have c := h3 v
    split_ifs at a b <;> omega
  have hsum := sum_le_sum fun v (_ : v ∈ (univ : Finset V)) => hv v
  have hmul := sum_nsmul univ 6 fun v => G.degree v
  simp only [smul_eq_mul] at hmul
  rw [sum_add_distrib, sum_add_distrib, sum_comm (f := fun u v => g u v), hmul,
    t1_sum_degrees] at hsum
  simp only [sum_const, card_univ, smul_eq_mul] at hsum
  omega

/-- **Kostochka–Yancey (Ore's conjecture for `k = 4`).** Every 4-critical graph satisfies
`ρ_G(V) ≤ 2`, i.e. `3 |E| ≥ 5 |V| - 2`. -/
theorem pot_univ_le_two : ∀ (N : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V),
    Fintype.card V = N → IsCritical4 G → pot G univ ≤ 2 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro V _ G hN hG
  by_contra hbig
  push Not at hbig
  have hsmall : SmallCritical N :=
    smallCritical_of_minimal N fun W _ H hW hH => ih _ hW W H rfl hH
  have hmin : MinCounter G := ⟨hG, hbig, hN ▸ hsmall⟩
  have h5 := discharging G hG.three_le_degree hmin.deg3_nbrs
  have hE : eIn G univ = G.edgeFinset.card := by
    unfold eIn; congr 1; exact filter_true_of_mem fun e _ v _ => mem_univ v
  have : pot G univ = 5 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) := by
    rw [pot, hE, card_univ]
  omega

/-- Edge form: every 4-critical graph has at least `(5|V| - 2)/3` edges. -/
theorem five_mul_card_le {V : Type} [Fintype V] (G : SimpleGraph V) (hG : IsCritical4 G) :
    5 * Fintype.card V ≤ 3 * G.edgeFinset.card + 2 := by
  have h := pot_univ_le_two _ V G rfl hG
  have hE : eIn G univ = G.edgeFinset.card := by
    unfold eIn; congr 1; exact filter_true_of_mem fun e _ v _ => mem_univ v
  rw [pot, hE, card_univ] at h
  omega

end Grotzsch
