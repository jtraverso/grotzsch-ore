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

/-- Ordered count of adjacent pairs `(a, b)` with `a ∈ S`, `b ∈ R`. -/
private def t2_cross {α : Type*} (G : SimpleGraph α) (S R : Finset α) : ℕ :=
  ∑ a ∈ S, ∑ b ∈ R, if G.Adj a b then 1 else 0

private lemma t2_two_eIn {W : Type*} [Fintype W] (G : SimpleGraph W) (R : Finset W) :
    2 * eIn G R = t2_cross G R R := by
  have h1 : t2_cross G R R = #((R ×ˢ R).filter fun p => G.Adj p.1 p.2) := by
    rw [card_filter, sum_product]; rfl
  rw [h1, card_eq_sum_card_fiberwise (f := fun p => s(p.1, p.2))
    (t := G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ R)]
  · rw [eIn, mul_comm, ← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun e he => ?_
    induction e using Sym2.ind with
    | _ a b =>
    simp only [mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Sym2.mem_iff,
      forall_eq_or_imp, forall_eq] at he
    obtain ⟨he, ha, hb⟩ := he
    have : ({x ∈ (R ×ˢ R).filter (fun p => G.Adj p.1 p.2) | s(x.1, x.2) = s(a, b)}) =
        {(a, b), (b, a)} := by
      ext ⟨x, y⟩
      simp only [mem_filter, mem_product, Sym2.eq_iff, mem_insert, mem_singleton,
        Prod.mk.injEq]
      constructor
      · rintro ⟨-, h⟩; exact h
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨⟨⟨ha, hb⟩, he⟩, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨⟨⟨hb, ha⟩, he.symm⟩, Or.inr ⟨rfl, rfl⟩⟩
    rw [this, card_pair]
    intro h
    simp only [Prod.mk.injEq] at h
    exact G.ne_of_adj he h.1
  · intro p hp
    simp only [coe_filter, mem_product] at hp
    simp only [coe_filter, SimpleGraph.mem_edgeFinset]
    refine ⟨hp.2, fun v hv => ?_⟩
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    exacts [hp.1.1, hp.1.2]

private lemma t2_two_pot {W : Type*} [Fintype W] (G : SimpleGraph W) (R : Finset W) :
    2 * pot G R = 10 * (R.card : ℤ) - 3 * (t2_cross G R R : ℤ) := by
  rw [pot, ← t2_two_eIn]; push_cast; linarith

private lemma t2_cross_union {α : Type*} [DecidableEq α] (G : SimpleGraph α) (S R : Finset α)
    (h : Disjoint S R) :
    t2_cross G (S ∪ R) (S ∪ R) = t2_cross G S S + t2_cross G R R + 2 * t2_cross G S R := by
  have hc : t2_cross G R S = t2_cross G S R := by
    unfold t2_cross; rw [sum_comm]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by
      simp only [G.adj_comm]
  unfold t2_cross at *
  simp only [sum_union h]
  rw [sum_add_distrib, sum_add_distrib, hc]; omega

private lemma t2_cross_map {α β : Type*} (H : SimpleGraph α) (G : SimpleGraph β) (f g : α ↪ β)
    (hf : ∀ a b, H.Adj a b ↔ G.Adj (f a) (g b)) (S R : Finset α) :
    t2_cross H S R = t2_cross G (S.map f) (R.map g) := by
  unfold t2_cross
  simp only [sum_map, hf]

private lemma t2_cross_top {α : Type*} (S : Finset α) :
    t2_cross (⊤ : SimpleGraph α) S S = S.card * (S.card - 1) := by
  unfold t2_cross
  refine sum_const_nat fun a ha => ?_
  simp only [SimpleGraph.top_adj, ← card_filter]
  rw [filter_ne, card_erase_of_mem ha]

private lemma t2_cross_le_top {α : Type*} (G : SimpleGraph α) (S : Finset α) :
    t2_cross G S S ≤ S.card * (S.card - 1) := by
  rw [← t2_cross_top]
  exact sum_le_sum fun a _ => sum_le_sum fun b _ => by
    by_cases h : G.Adj a b
    · simp [h, G.ne_of_adj h]
    · simp [h]

/-- Sets of size `2` and `3` have potential at least `7` and `6`. -/
private lemma t2_pot_small {W : Type*} [Fintype W] (G : SimpleGraph W) (R : Finset W) :
    (R.card = 2 → 7 ≤ pot G R) ∧ (R.card = 3 → 6 ≤ pot G R) := by
  have h := t2_two_pot G R
  have h' := t2_cross_le_top G R
  constructor
  · intro h2; rw [h2] at h h'; norm_num at h'; omega
  · intro h3; rw [h3] at h h'; norm_num at h'; omega

/-- The graph `Y(G, R, φ)` of Definition 7. -/
private def t2_Y (G : SimpleGraph V) (R : Finset V) (phi : V → Fin 3) :
    SimpleGraph ({v // v ∉ R} ⊕ Fin 3) where
  Adj x y := match x, y with
    | .inl a, .inl b => G.Adj a b
    | .inr i, .inr j => i ≠ j
    | .inl a, .inr i => ∃ w ∈ R, G.Adj a w ∧ phi w = i
    | .inr i, .inl a => ∃ w ∈ R, G.Adj a w ∧ phi w = i
  symm := ⟨fun x y h => by
    cases x <;> cases y <;> simp_all [G.adj_comm, eq_comm]⟩
  loopless := ⟨fun x h => by
    cases x <;> simp_all⟩

omit [Fintype V] in
/-- **Claim 8.** `Y(G, R, φ)` is not 3-colourable. -/
private lemma t2_Y_not_colorable (hc : ¬ G.Colorable 3) (R : Finset V) (phi : V → Fin 3)
    (hphi : ∀ u ∈ R, ∀ v ∈ R, G.Adj u v → phi u ≠ phi v) : ¬ (t2_Y G R phi).Colorable 3 := by
  rintro ⟨c⟩
  have hσ : Function.Injective fun i => c (.inr i) := by
    intro i j h
    by_contra hij
    exact c.valid (show (t2_Y G R phi).Adj (.inr i) (.inr j) from hij) h
  apply hc
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => if h : v ∈ R then c (.inr (phi v)) else c (.inl ⟨v, h⟩)) ?_⟩
  intro u v huv
  by_cases hu : u ∈ R <;> by_cases hv : v ∈ R <;> simp only [hu, hv, ↓reduceDIte]
  · exact fun h => hphi u hu v hv huv (hσ h)
  · exact fun h => c.valid (show (t2_Y G R phi).Adj (.inr (phi u)) (.inl ⟨v, hv⟩) from
      ⟨u, hu, huv.symm, rfl⟩) h
  · exact fun h => c.valid (show (t2_Y G R phi).Adj (.inl ⟨u, hu⟩) (.inr (phi v)) from
      ⟨v, hv, huv, rfl⟩) h
  · exact c.valid (show (t2_Y G R phi).Adj (.inl ⟨u, hu⟩) (.inl ⟨v, hv⟩) from huv)

/-- The core potential computation of Claims 9 and 10. -/
private lemma t2_core (hG : MinCounter G) (R : Finset V) (hR : R ≠ univ) (h4 : 4 ≤ R.card)
    (phi : V → Fin 3) (hphi : ∀ u ∈ R, ∀ v ∈ R, G.Adj u v → phi u ≠ phi v) :
    ∃ (A : Finset V) (B : Finset (Fin 3)), Disjoint A R ∧ B.Nonempty ∧
      pot G (A ∪ R) + 3 * ((∑ a ∈ A, ∑ w ∈ R,
        if G.Adj a w ∧ phi w ∉ B then 1 else 0 : ℕ) : ℤ) + 5 ≤ 2 + pot G R ∧
      (2 ≤ B.card → pot G (A ∪ R) + 6 ≤ 2 + pot G R) := by
  obtain ⟨z0, hz0⟩ : ∃ z, z ∉ R := by
    by_contra h; push Not at h; exact hR (eq_univ_of_forall h)
  obtain ⟨r0, hr0⟩ : R.Nonempty := card_pos.1 (by omega)
  set Y := t2_Y G R phi with hY
  have hcard : Fintype.card ({v // v ∉ R} ⊕ Fin 3) < Fintype.card V := by
    have := card_le_univ R
    simp only [Fintype.card_sum, Fintype.card_fin]
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
    omega
  obtain ⟨S, hSne, hSpot, hScol⟩ :=
    hG.small _ Y hcard (t2_Y_not_colorable hG.crit.not_colorable R phi hphi)
  set A0 : Finset {v // v ∉ R} := S.preimage Sum.inl Sum.inl_injective.injOn
  set B : Finset (Fin 3) := S.preimage Sum.inr Sum.inr_injective.injOn
  let eL : {v // v ∉ R} ↪ ({v // v ∉ R} ⊕ Fin 3) := ⟨Sum.inl, Sum.inl_injective⟩
  let eR : Fin 3 ↪ ({v // v ∉ R} ⊕ Fin 3) := ⟨Sum.inr, Sum.inr_injective⟩
  let eV : {v // v ∉ R} ↪ V := Function.Embedding.subtype _
  have hS : S = A0.map eL ∪ B.map eR := by
    ext x; cases x <;> simp [A0, B, eL, eR]
  have hdisjS : Disjoint (A0.map eL) (B.map eR) := by
    rw [disjoint_left]
    intro x hx hx'
    simp only [mem_map] at hx hx'
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨i, _, h⟩ := hx'
    cases h
  set A := A0.map eV with hA
  have hdisj : Disjoint A R := by
    rw [disjoint_left]
    intro x hx
    simp only [hA, mem_map] at hx
    obtain ⟨a, _, rfl⟩ := hx
    exact a.2
  have hBne : B.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hB
    apply hScol
    obtain ⟨c⟩ := hG.crit.vertex r0
    let f : ({v // v ∉ R} ⊕ Fin 3) → V := Sum.elim Subtype.val (fun _ => z0)
    have hf : ∀ x, f x ≠ r0 := by
      intro x
      cases x with
      | inl a => exact show a.1 ≠ r0 from fun h => a.2 (h ▸ hr0)
      | inr i => exact show z0 ≠ r0 from fun h => hz0 (h ▸ hr0)
    refine ⟨SimpleGraph.Coloring.mk (fun x => c ⟨f x.1, hf x.1⟩) ?_⟩
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    rw [mem_coe, hS, hB, map_empty, union_empty, mem_map] at hx hy
    obtain ⟨a, -, rfl⟩ := hx
    obtain ⟨b, -, rfl⟩ := hy
    exact c.valid (show G.Adj a b from hxy)
  set cY := t2_cross Y (A0.map eL) (B.map eR)
  set cin := ∑ a ∈ A, ∑ w ∈ R, if G.Adj a w ∧ phi w ∈ B then 1 else 0
  set cout := ∑ a ∈ A, ∑ w ∈ R, if G.Adj a w ∧ phi w ∉ B then 1 else 0
  have h1 : S.card = A0.card + B.card := by
    rw [hS, card_union_of_disjoint hdisjS, card_map, card_map]
  have h2 : t2_cross Y S S = t2_cross Y (A0.map eL) (A0.map eL) +
      t2_cross Y (B.map eR) (B.map eR) + 2 * cY := by
    rw [hS]; exact t2_cross_union _ _ _ hdisjS
  have h3 : t2_cross Y (A0.map eL) (A0.map eL) = t2_cross G A A := by
    rw [← t2_cross_map (G.comap eV) Y eL eL (fun a b => Iff.rfl),
      t2_cross_map (G.comap eV) G eV eV (fun a b => Iff.rfl)]
  have h4' : t2_cross Y (B.map eR) (B.map eR) = B.card * (B.card - 1) := by
    rw [← t2_cross_map ⊤ Y eR eR (fun a b => Iff.rfl), t2_cross_top]
  have h5 : cY ≤ cin := by
    simp only [cY, cin, t2_cross, hA, sum_map]
    refine sum_le_sum fun a _ => ?_
    calc (∑ i ∈ B, if Y.Adj (eL a) (eR i) then 1 else 0)
        ≤ ∑ i ∈ B, ∑ w ∈ R, if G.Adj (eV a) w ∧ phi w = i then 1 else 0 := by
          refine sum_le_sum fun i _ => ?_
          split_ifs with h
          · obtain ⟨w, hw, hadj, rfl⟩ := h
            refine le_trans ?_ (single_le_sum (f := fun x => if G.Adj (eV a) x ∧ phi x = phi w
              then 1 else 0) (fun _ _ => Nat.zero_le _) hw)
            rw [ite_eq_left (show G.Adj (eV a) w ∧ phi w = phi w from ⟨hadj, rfl⟩)]
          · exact Nat.zero_le _
      _ = ∑ w ∈ R, ∑ i ∈ B, if G.Adj (eV a) w ∧ phi w = i then 1 else 0 := sum_comm
      _ = _ := sum_congr rfl fun w _ => by
          by_cases hadj : G.Adj (eV a) w <;> simp [hadj, sum_ite_eq]
  have hsplit : t2_cross G A R = cin + cout := by
    simp only [cin, cout, t2_cross]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun w _ => ?_
    by_cases ha : G.Adj a w <;> by_cases hb : phi w ∈ B <;> simp [ha, hb]
  have hT := t2_two_pot G (A ∪ R)
  rw [card_union_of_disjoint hdisj, t2_cross_union _ _ _ hdisj, hsplit] at hT
  have hRp := t2_two_pot G R
  have hYp := t2_two_pot Y S
  rw [h1, h2, h3, h4'] at hYp
  have hAc : A.card = A0.card := card_map _
  have hBle : B.card ≤ 3 := (card_le_univ B).trans (by simp)
  have hB1 : 1 ≤ B.card := card_pos.2 hBne
  refine ⟨A, B, hdisj, hBne, ?_, ?_⟩
  · have : 10 * (B.card : ℤ) - 3 * ((B.card * (B.card - 1) : ℕ) : ℤ) ≥ 10 := by
      rcases (by omega : B.card = 1 ∨ B.card = 2 ∨ B.card = 3) with h | h | h <;>
        rw [h] <;> norm_num
    push_cast at hT hYp this ⊢
    omega
  · intro hB2
    have : 10 * (B.card : ℤ) - 3 * ((B.card * (B.card - 1) : ℕ) : ℤ) ≥ 12 := by
      rcases (by omega : B.card = 2 ∨ B.card = 3) with h | h <;>
        rw [h] <;> norm_num
    push_cast at hT hYp this ⊢
    omega

/-- **Claim 9.** Every proper subset `R` with `|R| ≥ 2` has potential at least `6`. -/
theorem MinCounter.claim9 (hG : MinCounter G) (R : Finset V) (hR : R ≠ univ)
    (h2 : 2 ≤ R.card) : 6 ≤ pot G R := by
  by_contra hlt
  push Not at hlt
  set P := (univ : Finset (Finset V)).filter fun S => S ≠ univ ∧ 2 ≤ S.card with hP
  have hRP : R ∈ P := mem_filter.2 ⟨mem_univ _, hR, h2⟩
  obtain ⟨R0, hR0P, hmin⟩ := exists_min_image P (pot G) ⟨R, hRP⟩
  obtain ⟨-, hR0, h20⟩ := mem_filter.1 hR0P
  have hle : pot G R0 ≤ 5 := (hmin R hRP).trans (by omega)
  have h40 : 4 ≤ R0.card := by
    have hs := t2_pot_small G R0
    by_contra h
    push Not at h
    rcases (by omega : R0.card = 2 ∨ R0.card = 3) with h' | h'
    · have := hs.1 h'; omega
    · have := hs.2 h'; omega
  obtain ⟨v0, hv0⟩ : ∃ v, v ∉ R0 := by
    by_contra h; push Not at h; exact hR0 (eq_univ_of_forall h)
  obtain ⟨c⟩ := hG.crit.vertex v0
  let phi : V → Fin 3 := fun v => if h : v ≠ v0 then c ⟨v, h⟩ else 0
  have hphi : ∀ u ∈ R0, ∀ v ∈ R0, G.Adj u v → phi u ≠ phi v := by
    intro u hu v hv huv
    have hu' : u ≠ v0 := fun h => hv0 (h ▸ hu)
    have hv' : v ≠ v0 := fun h => hv0 (h ▸ hv)
    simp only [phi, hu', hv', ne_eq, not_false_eq_true, ↓reduceDIte]
    exact c.valid (show G.Adj u v from huv)
  obtain ⟨A, B, -, -, hpot, -⟩ := t2_core hG R0 hR0 h40 phi hphi
  by_cases hT : A ∪ R0 = univ
  · have := hG.big
    rw [hT] at hpot
    omega
  · have := hmin (A ∪ R0)
      (mem_filter.2 ⟨mem_univ _, hT, le_trans h20 (card_le_card subset_union_right)⟩)
    omega

/-- If at most one vertex `u1` of `R` has neighbours outside `R`, then `G` is 3-colourable. -/
private lemma t2_colorable_of_cut (hc : IsCritical4 G) (R : Finset V) (hR : R ≠ univ)
    (u1 r : V) (hu1 : u1 ∈ R) (hr : r ∈ R) (hru : r ≠ u1)
    (hcut : ∀ u ∈ R, ∀ z ∉ R, G.Adj u z → u = u1) : G.Colorable 3 := by
  obtain ⟨v0, hv0⟩ : ∃ v, v ∉ R := by
    by_contra h; push Not at h; exact hR (eq_univ_of_forall h)
  obtain ⟨c1⟩ := hc.vertex v0
  obtain ⟨c2⟩ := hc.vertex r
  let phi : V → Fin 3 := fun v => if h : v ≠ v0 then c1 ⟨v, h⟩ else 0
  let psi : V → Fin 3 := fun v => if h : v ≠ r then c2 ⟨v, h⟩ else 0
  have key1 : ∀ u ∈ R, ∀ v ∈ R, G.Adj u v → phi u ≠ phi v := by
    intro u hu v hv huv
    have hu' : u ≠ v0 := fun h => hv0 (h ▸ hu)
    have hv' : v ≠ v0 := fun h => hv0 (h ▸ hv)
    simp only [phi, hu', hv', ne_eq, not_false_eq_true, ↓reduceDIte]
    exact c1.valid (show G.Adj u v from huv)
  have key2 : ∀ u v, u ≠ r → v ≠ r → G.Adj u v → psi u ≠ psi v := by
    intro u v hu' hv' huv
    simp only [psi, hu', hv', ne_eq, not_false_eq_true, ↓reduceDIte]
    exact c2.valid (show G.Adj u v from huv)
  let σ := Equiv.swap (psi u1) (phi u1)
  have hσ : σ (psi u1) = phi u1 := Equiv.swap_apply_left _ _
  have hu1r : u1 ≠ r := Ne.symm hru
  refine ⟨SimpleGraph.Coloring.mk (fun v => if v ∈ R then phi v else σ (psi v)) ?_⟩
  intro u v huv
  by_cases hu : u ∈ R <;> by_cases hv : v ∈ R <;> simp only [hu, hv, ↓reduceIte]
  · exact key1 u hu v hv huv
  · obtain rfl := hcut u hu v hv huv
    rw [← hσ]
    exact fun h => key2 u v hu1r (fun h' => hv (h' ▸ hr)) huv (σ.injective h)
  · obtain rfl := hcut v hv u hu huv.symm
    rw [← hσ]
    exact fun h => key2 u v (fun h' => hu (h' ▸ hr)) hu1r huv (σ.injective h)
  · exact fun h => key2 u v (fun h' => hu (h' ▸ hr)) (fun h' => hv (h' ▸ hr)) huv
      (σ.injective h)

/-- `G` is 2-connected in the sense needed for Claim 10: a proper subset with at least two
vertices has two distinct vertices with neighbours outside it. -/
private lemma t2_boundary (hc : IsCritical4 G) (R : Finset V) (hR : R ≠ univ)
    (h2 : 2 ≤ R.card) :
    ∃ u1 ∈ R, ∃ u2 ∈ R, u1 ≠ u2 ∧ (∃ z ∉ R, G.Adj u1 z) ∧ (∃ z ∉ R, G.Adj u2 z) := by
  by_cases hb : ∃ u ∈ R, ∃ z ∉ R, G.Adj u z
  · obtain ⟨u1, hu1, z1, hz1, h1⟩ := hb
    obtain ⟨r, hr, hru⟩ := exists_mem_ne (by omega : 1 < R.card) u1
    by_contra hno
    apply hc.not_colorable
    refine t2_colorable_of_cut hc R hR u1 r hu1 hr hru ?_
    intro u hu z hz huz
    by_contra hne
    exact hno ⟨u, hu, u1, hu1, hne, ⟨z, hz, huz⟩, ⟨z1, hz1, h1⟩⟩
  · exfalso
    obtain ⟨u1, hu1⟩ : R.Nonempty := card_pos.1 (by omega)
    obtain ⟨r, hr, hru⟩ := exists_mem_ne (by omega : 1 < R.card) u1
    apply hc.not_colorable
    refine t2_colorable_of_cut hc R hR u1 r hu1 hr hru ?_
    intro u hu z hz huz
    exact absurd ⟨u, hu, z, hz, huz⟩ hb

/-- A 3-colouring of `G[R] + u1u2` (exists by hypothesis (3) and Claim 9). -/
private lemma t2_color_plus_edge (hG : MinCounter G) (R : Finset V) (hR : R ≠ univ)
    (u1 u2 : V) (hu1 : u1 ∈ R) (hu2 : u2 ∈ R) (hne : u1 ≠ u2) :
    ∃ phi : V → Fin 3, (∀ u ∈ R, ∀ v ∈ R, G.Adj u v → phi u ≠ phi v) ∧ phi u1 ≠ phi u2 := by
  let a1 : R := ⟨u1, hu1⟩
  let a2 : R := ⟨u2, hu2⟩
  let eV : R ↪ V := Function.Embedding.subtype _
  let H : SimpleGraph R := SimpleGraph.fromRel fun a b => G.Adj a b ∨ (a = a1 ∧ b = a2)
  have hHadj : ∀ a b, H.Adj a b ↔
      a ≠ b ∧ ((G.Adj a b ∨ (a = a1 ∧ b = a2)) ∨ (G.Adj b a ∨ (b = a1 ∧ a = a2))) :=
    fun a b => SimpleGraph.fromRel_adj _ _ _
  have hcardR : Fintype.card R < Fintype.card V := by
    rw [Fintype.card_coe, ← card_univ]
    exact card_lt_card (ssubset_univ_iff.2 hR)
  have hcol : H.Colorable 3 := by
    refine hG.small.smallColorable R H hcardR fun U hU => ?_
    have hp := t2_two_pot H U
    rcases (by have := card_pos.2 hU; omega : U.card = 1 ∨ 2 ≤ U.card) with h1 | h2'
    · obtain ⟨a, rfl⟩ := card_eq_one.1 h1
      have : t2_cross H {a} {a} = 0 := by simp [t2_cross]
      rw [this, h1] at hp
      omega
    · have hU' : U.map eV ≠ univ := by
        intro h
        apply hR
        refine eq_univ_of_forall fun v => ?_
        have : v ∈ U.map eV := h ▸ mem_univ v
        obtain ⟨b, -, rfl⟩ := mem_map.1 this
        exact b.2
      have h9 := hG.claim9 (U.map eV) hU' (by rw [card_map]; exact h2')
      have hpG := t2_two_pot G (U.map eV)
      rw [card_map, ← t2_cross_map (G.comap eV) G eV eV (fun _ _ => Iff.rfl)] at hpG
      have hpair : ∀ x y : R, (∑ a ∈ U, ∑ b ∈ U, if a = x ∧ b = y then 1 else 0) ≤ 1 := by
        intro x y
        calc (∑ a ∈ U, ∑ b ∈ U, if a = x ∧ b = y then 1 else 0)
            ≤ ∑ a ∈ U, if a = x then 1 else 0 := sum_le_sum fun a _ => by
              by_cases ha : a = x
              · simp only [ha, true_and, ↓reduceIte]
                rw [sum_ite_eq']
                split_ifs <;> omega
              · simp [ha]
          _ ≤ 1 := by
              rw [sum_ite_eq']
              split_ifs <;> omega
      have hle : t2_cross H U U ≤ t2_cross (G.comap eV) U U +
          (∑ a ∈ U, ∑ b ∈ U, if a = a1 ∧ b = a2 then 1 else 0) +
          (∑ a ∈ U, ∑ b ∈ U, if a = a2 ∧ b = a1 then 1 else 0) := by
        simp only [t2_cross, ← sum_add_distrib]
        refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
        by_cases hab : H.Adj a b
        · rw [ite_eq_left hab]
          rw [hHadj] at hab
          rcases hab with ⟨-, (h | h) | (h | h)⟩
          · rw [ite_eq_left (show (G.comap eV).Adj a b from h)]; omega
          · rw [ite_eq_left h]; omega
          · rw [ite_eq_left (show (G.comap eV).Adj a b from h.symm)]; omega
          · rw [ite_eq_left (show a = a2 ∧ b = a1 from ⟨h.2, h.1⟩)]; omega
        · rw [ite_eq_right hab]; omega
      have := hpair a1 a2
      have := hpair a2 a1
      omega
  obtain ⟨c⟩ := hcol
  refine ⟨fun v => if h : v ∈ R then c ⟨v, h⟩ else 0, ?_, ?_⟩
  · intro u hu v hv huv
    simp only [hu, hv, ↓reduceDIte]
    exact c.valid ((hHadj _ _).2
      ⟨fun h => G.ne_of_adj huv (congrArg Subtype.val h), Or.inl (Or.inl huv)⟩)
  · simp only [hu1, hu2, ↓reduceDIte]
    exact c.valid ((hHadj a1 a2).2
      ⟨fun h => hne (congrArg Subtype.val h), Or.inl (Or.inr ⟨rfl, rfl⟩)⟩)

/-- **Claim 10.** A proper subset `R` with `|R| ≥ 2` and potential `≤ 6` spans a triangle. -/
theorem MinCounter.claim10 (hG : MinCounter G) (R : Finset V) (hR : R ≠ univ)
    (h2 : 2 ≤ R.card) (h6 : pot G R ≤ 6) : R.card = 3 ∧ eIn G R = 3 := by
  have h9 := hG.claim9 R hR h2
  have h6' : pot G R = 6 := by omega
  have hs := t2_pot_small G R
  rcases (by omega : R.card = 2 ∨ R.card = 3 ∨ 4 ≤ R.card) with h | h | h
  · have := hs.1 h; omega
  · refine ⟨h, ?_⟩
    unfold pot at h6'
    rw [h] at h6'
    omega
  · exfalso
    obtain ⟨u1, hu1, u2, hu2, hne, ⟨z1, hz1, hadj1⟩, ⟨z2, hz2, hadj2⟩⟩ :=
      t2_boundary hG.crit R hR h2
    obtain ⟨phi, hphi, hphi12⟩ := t2_color_plus_edge hG R hR u1 u2 hu1 hu2 hne
    obtain ⟨A, B, -, hBne, hpot1, hpot2⟩ := t2_core hG R hR h phi hphi
    have hbig := hG.big
    rcases (by have := card_pos.2 hBne; omega : B.card = 1 ∨ 2 ≤ B.card) with hB | hB
    · obtain ⟨i, rfl⟩ := card_eq_one.1 hB
      by_cases hT : A ∪ R = univ
      · obtain ⟨u, hu, z, hz, hzu, hui⟩ : ∃ u ∈ R, ∃ z ∉ R, G.Adj u z ∧ phi u ≠ i := by
          by_cases h1 : phi u1 = i
          · exact ⟨u2, hu2, z2, hz2, hadj2, fun h => hphi12 (h1.trans h.symm)⟩
          · exact ⟨u1, hu1, z1, hz1, hadj1, h1⟩
        have hzA : z ∈ A := by
          have : z ∈ A ∪ R := hT ▸ mem_univ z
          rcases mem_union.1 this with h' | h'
          exacts [h', absurd h' hz]
        have hext : 1 ≤ ∑ a ∈ A, ∑ w ∈ R,
            if G.Adj a w ∧ phi w ∉ ({i} : Finset (Fin 3)) then 1 else 0 := by
          refine le_trans ?_ (single_le_sum (f := fun a => ∑ w ∈ R,
            if G.Adj a w ∧ phi w ∉ ({i} : Finset (Fin 3)) then 1 else 0)
            (fun _ _ => Nat.zero_le _) hzA)
          refine le_trans ?_ (single_le_sum (f := fun w =>
            if G.Adj z w ∧ phi w ∉ ({i} : Finset (Fin 3)) then 1 else 0)
            (fun _ _ => Nat.zero_le _) hu)
          rw [ite_eq_left ⟨hzu.symm, by simpa using hui⟩]
        rw [hT] at hpot1
        omega
      · have := hG.claim9 (A ∪ R) hT (le_trans h2 (card_le_card subset_union_right))
        omega
    · have := hpot2 hB
      by_cases hT : A ∪ R = univ
      · rw [hT] at this
        omega
      · have := hG.claim9 (A ∪ R) hT (le_trans h2 (card_le_card subset_union_right))
        omega

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

/-- The neighbourhood of a degree-3 vertex `x` with a known neighbour `y`. -/
private lemma t3_nbr2 {x y : V} (hx : G.degree x = 3) (hxy : G.Adj x y) :
    ∃ a b, a ≠ b ∧ a ≠ y ∧ b ≠ y ∧ G.Adj x a ∧ G.Adj x b ∧
      ∀ w, G.Adj x w → w = y ∨ w = a ∨ w = b := by
  have hy : y ∈ G.neighborFinset x := (G.mem_neighborFinset x y).2 hxy
  have hc : ((G.neighborFinset x).erase y).card = 2 := by
    rw [card_erase_of_mem hy, G.card_neighborFinset_eq_degree, hx]
  obtain ⟨a, b, hab, he⟩ := card_eq_two.1 hc
  have ha : a ∈ (G.neighborFinset x).erase y := he ▸ mem_insert_self a {b}
  have hb : b ∈ (G.neighborFinset x).erase y := he ▸ mem_insert_of_mem (mem_singleton_self b)
  rw [mem_erase, G.mem_neighborFinset] at ha hb
  refine ⟨a, b, hab, ha.1, hb.1, ha.2, hb.2, fun w hw => ?_⟩
  by_cases hwy : w = y
  · exact Or.inl hwy
  · have : w ∈ (G.neighborFinset x).erase y :=
      mem_erase.2 ⟨hwy, (G.mem_neighborFinset x w).2 hw⟩
    rw [he, mem_insert, mem_singleton] at this
    exact Or.inr this

/-- The neighbourhood of a degree-3 vertex `x` with two known neighbours `y`, `z`. -/
private lemma t3_nbr3 {x y z : V} (hx : G.degree x = 3) (hxy : G.Adj x y) (hxz : G.Adj x z)
    (hyz : y ≠ z) :
    ∃ a, a ≠ y ∧ a ≠ z ∧ G.Adj x a ∧ ∀ w, G.Adj x w → w = y ∨ w = z ∨ w = a := by
  obtain ⟨a, b, hab, hay, hby, ha, hb, h⟩ := t3_nbr2 hx hxy
  rcases h z hxz with h1 | h1 | h1
  · exact absurd h1.symm hyz
  · subst h1
    exact ⟨b, hby, hab.symm, hb, fun w hw => by rcases h w hw with h2 | h2 | h2 <;> tauto⟩
  · subst h1
    exact ⟨a, hay, hab, ha, fun w hw => by rcases h w hw with h2 | h2 | h2 <;> tauto⟩

omit [Fintype V] in
/-- Extending a colouring of `G - x - y` to the adjacent vertices `x`, `y`. -/
private lemma t3_glue {x y : V} (phi : V → Fin 3) (cx cy : Fin 3) (hcxy : cx ≠ cy)
    (hphi : ∀ s t, s ≠ x → s ≠ y → t ≠ x → t ≠ y → G.Adj s t → phi s ≠ phi t)
    (hx : ∀ t, G.Adj x t → t ≠ y → cx ≠ phi t)
    (hy : ∀ t, G.Adj y t → t ≠ x → cy ≠ phi t) : G.Colorable 3 := by
  refine ⟨SimpleGraph.Coloring.mk (fun w => if w = x then cx else if w = y then cy else phi w) ?_⟩
  intro s t hst
  have hts : t ≠ s := (G.ne_of_adj hst).symm
  by_cases hsx : s = x
  · rw [ite_eq_left hsx, ite_eq_right (hsx ▸ hts)]
    by_cases hty : t = y
    · rw [ite_eq_left hty]; exact hcxy
    · rw [ite_eq_right hty]; exact hx t (hsx ▸ hst) hty
  by_cases hsy : s = y
  · rw [ite_eq_right hsx, ite_eq_left hsy]
    by_cases htx : t = x
    · rw [ite_eq_left htx]; exact hcxy.symm
    · rw [ite_eq_right htx, ite_eq_right (hsy ▸ hts)]; exact hy t (hsy ▸ hst) htx
  rw [ite_eq_right hsx, ite_eq_right hsy]
  by_cases htx : t = x
  · rw [ite_eq_left htx]; exact (hx s (htx ▸ hst.symm) hsy).symm
  by_cases hty : t = y
  · rw [ite_eq_right htx, ite_eq_left hty]; exact (hy s (hty ▸ hst.symm) hsx).symm
  rw [ite_eq_right htx, ite_eq_right hty]
  exact hphi s t hsx hsy htx hty hst

/-- **Claim 12.** Each triangle contains at most one vertex of degree 3. -/
theorem MinCounter.claim12 (hG : MinCounter G) {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hxz : G.Adj x z) (hx : G.degree x = 3) (hy : G.degree y = 3) : False := by
  have hxy' := G.ne_of_adj hxy
  have hxz' := G.ne_of_adj hxz
  have hyz' := G.ne_of_adj hyz
  obtain ⟨a, hay, haz, hxa, hNx⟩ := t3_nbr3 hx hxy hxz hyz'
  obtain ⟨b, hbx, hbz, hyb, hNy⟩ := t3_nbr3 hy hxy.symm hyz hxz'
  have hax : a ≠ x := (G.ne_of_adj hxa).symm
  have hby : b ≠ y := (G.ne_of_adj hyb).symm
  have hab : a ≠ b := by
    rintro rfl
    have h4 : ({x, y, z, a} : Finset V).card = 4 := by
      rw [card_insert_of_notMem (by simp [hxy', hxz', hax.symm]),
        card_insert_of_notMem (by simp [hyz', hay.symm]), card_pair haz.symm]
    have h11 := hG.claim11 _ h4
    have h2 := t2_two_eIn G ({x, y, z, a} : Finset V)
    have hc : 10 ≤ t2_cross G ({x, y, z, a} : Finset V) {x, y, z, a} := by
      simp [t2_cross, sum_insert, hxy', hxz', hax.symm, hyz', hay.symm, haz.symm, hxy, hyz,
        hxz, hxa, hyb, hxy.symm, hyz.symm, hxz.symm, hxa.symm, hyb.symm]
      omega
    omega
  have hmem : ∀ w, w ∈ (univ.erase x).erase y ↔ w ≠ x ∧ w ≠ y := by
    intro w; simp only [mem_erase, mem_univ, and_true]; tauto
  have hRu : (univ.erase x).erase y ≠ univ := fun h =>
    ((hmem x).1 (by rw [h]; exact mem_univ x)).1 rfl
  obtain ⟨phi, hphi, hphiab⟩ := t2_color_plus_edge hG _ hRu a b ((hmem a).2 ⟨hax, hay⟩)
    ((hmem b).2 ⟨hbx, hby⟩) hab
  have key : ∀ p q r : Fin 3, p ≠ q → ∃ cx cy : Fin 3,
      cx ≠ p ∧ cx ≠ r ∧ cy ≠ q ∧ cy ≠ r ∧ cx ≠ cy := by decide
  obtain ⟨cx, cy, h1, h2, h3, h4, h5⟩ := key _ _ (phi z) hphiab
  apply hG.crit.not_colorable
  refine t3_glue phi cx cy h5
    (fun s t hsx hsy htx hty hst => hphi s ((hmem s).2 ⟨hsx, hsy⟩) t ((hmem t).2 ⟨htx, hty⟩) hst)
    ?_ ?_
  · intro t ht hty
    rcases hNx t ht with rfl | rfl | rfl
    · exact absurd rfl hty
    · exact h2
    · exact h1
  · intro t ht htx
    rcases hNy t ht with rfl | rfl | rfl
    · exact absurd rfl htx
    · exact h4
    · exact h3

/-- The vertex set of `G - x - y - v`. -/
private def t3_R (x y v : V) : Finset V := ((univ.erase x).erase y).erase v

/-- The graph `G - x - y` in which `v` is merged into `u`. -/
private def t3_G' (H : SimpleGraph V) (x y v u : V) : SimpleGraph (t3_R x y v) :=
  SimpleGraph.fromRel fun a b => H.Adj a b ∨ ((a : V) = u ∧ H.Adj v b)

private lemma t3_mem {x y v w : V} : w ∈ t3_R x y v ↔ w ≠ x ∧ w ≠ y ∧ w ≠ v := by
  simp only [t3_R, mem_erase, mem_univ, and_true]; tauto

/-- A 3-colouring of the merged graph extends to a 3-colouring of `G`. -/
private lemma t3_extend {x y u v p q : V} (hxu : G.Adj x u) (huv : u ≠ v) (huy : u ≠ y)
    (hnuv : ¬ G.Adj u v) (hNx : ∀ w, G.Adj x w → w = y ∨ w = u ∨ w = v)
    (hNy : ∀ w, G.Adj y w → w = x ∨ w = p ∨ w = q)
    (hcol : (t3_G' G x y v u).Colorable 3) : G.Colorable 3 := by
  obtain ⟨c⟩ := hcol
  have hux : u ≠ x := (G.ne_of_adj hxu).symm
  have huR : u ∈ t3_R x y v := t3_mem.2 ⟨hux, huy, huv⟩
  have hvR : v ∉ t3_R x y v := fun h => (t3_mem.1 h).2.2 rfl
  let psi : V → Fin 3 := fun w => if h : w ∈ t3_R x y v then c ⟨w, h⟩ else c ⟨u, huR⟩
  have hpsiv : psi v = psi u := by simp only [psi, dite_eq_right hvR, dite_eq_left huR]
  have key : ∀ s t, s ≠ x → s ≠ y → t ≠ x → t ≠ y → s ≠ v → G.Adj s t → psi s ≠ psi t := by
    intro s t hsx hsy htx hty hsv hst
    have hsR : s ∈ t3_R x y v := t3_mem.2 ⟨hsx, hsy, hsv⟩
    by_cases htv : t = v
    · have hsu : s ≠ u := fun h => hnuv (h ▸ htv ▸ hst)
      have ht : psi t = c ⟨u, huR⟩ := by rw [htv, hpsiv]; simp only [psi, dite_eq_left huR]
      rw [ht]
      simp only [psi, dite_eq_left hsR]
      apply c.valid
      rw [t3_G', SimpleGraph.fromRel_adj]
      exact ⟨fun h => hsu (congrArg Subtype.val h), Or.inr (Or.inr ⟨rfl, htv ▸ hst.symm⟩)⟩
    · have htR : t ∈ t3_R x y v := t3_mem.2 ⟨htx, hty, htv⟩
      simp only [psi, dite_eq_left hsR, dite_eq_left htR]
      apply c.valid
      rw [t3_G', SimpleGraph.fromRel_adj]
      exact ⟨fun h => G.ne_of_adj hst (congrArg Subtype.val h), Or.inl (Or.inl hst)⟩
  have hpsi : ∀ s t, s ≠ x → s ≠ y → t ≠ x → t ≠ y → G.Adj s t → psi s ≠ psi t := by
    intro s t hsx hsy htx hty hst
    by_cases hsv : s = v
    · have htv : t ≠ v := fun h => G.ne_of_adj hst (hsv.trans h.symm)
      exact (key t s htx hty hsx hsy htv hst.symm).symm
    · exact key s t hsx hsy htx hty hsv hst
  have hch : ∀ a b d : Fin 3, ∃ cy cx : Fin 3, cy ≠ a ∧ cy ≠ b ∧ cx ≠ cy ∧ cx ≠ d := by decide
  obtain ⟨cy, cx, h1, h2, h3, h4⟩ := hch (psi p) (psi q) (psi u)
  refine t3_glue psi cx cy h3 hpsi ?_ ?_
  · intro t ht hty
    rcases hNx t ht with rfl | rfl | rfl
    · exact absurd rfl hty
    · exact h4
    · rw [hpsiv]; exact h4
  · intro t ht htx
    rcases hNy t ht with rfl | rfl | rfl
    · exact absurd rfl htx
    · exact h1
    · exact h2

/-- The potential estimate for un-merging a set containing the merged vertex. -/
private lemma t3_pot {x y u v : V} (hxu : G.Adj x u) (hxv : G.Adj x v) (hvx : v ≠ x)
    (hvy : v ≠ y) (hxy : x ≠ y)
    (huR : u ∈ t3_R x y v) (S : Finset (t3_R x y v)) (hu0 : (⟨u, huR⟩ : t3_R x y v) ∈ S) :
    ∃ T : Finset V, y ∉ T ∧ T.card = S.card + 2 ∧ pot G T ≤ pot (t3_G' G x y v u) S + 4 := by
  set S' := S.map (Function.Embedding.subtype (· ∈ t3_R x y v)) with hS'
  have hdisj : Disjoint S' {v, x} := by
    rw [disjoint_iff_ne]
    rintro a ha b hb rfl
    obtain ⟨c, -, rfl⟩ := mem_map.1 ha
    have := t3_mem.1 c.2
    rw [mem_insert, mem_singleton] at hb
    rcases hb with h | h
    exacts [this.2.2 h, this.1 h]
  have hcard : (S' ∪ {v, x}).card = S.card + 2 := by
    rw [card_union_of_disjoint hdisj, card_map, card_pair hvx]
  refine ⟨S' ∪ {v, x}, ?_, hcard, ?_⟩
  · rw [mem_union, mem_insert, mem_singleton]
    rintro (h | h | h)
    · obtain ⟨c, -, hc⟩ := mem_map.1 h
      exact (t3_mem.1 c.2).2.1 hc
    · exact hvy h.symm
    · exact hxy h.symm
  have hpT := t2_two_pot G (S' ∪ {v, x})
  have hpS := t2_two_pot (t3_G' G x y v u) S
  have hU := t2_cross_union G S' {v, x} hdisj
  have hC := t2_cross_map (G.comap (Function.Embedding.subtype (· ∈ t3_R x y v))) G
    (Function.Embedding.subtype _) (Function.Embedding.subtype _) (fun _ _ => Iff.rfl) S S
  rw [← hS'] at hC
  set N := ∑ a ∈ S, if G.Adj (a : V) v then 1 else 0 with hN
  have h1 : 2 ≤ t2_cross G {v, x} {v, x} := by
    simp [t2_cross, sum_pair hvx, hxv, hxv.symm]
  have h2 : N + 1 ≤ t2_cross G S' {v, x} := by
    have : t2_cross G S' {v, x} = N + ∑ a ∈ S, if G.Adj (a : V) x then 1 else 0 := by
      simp only [t2_cross, sum_pair hvx, hS', sum_map, sum_add_distrib, hN]
      rfl
    rw [this]
    have : 1 ≤ ∑ a ∈ S, if G.Adj (a : V) x then 1 else 0 := by
      refine le_trans ?_ (single_le_sum (f := fun a : t3_R x y v =>
        if G.Adj (a : V) x then 1 else 0) (fun _ _ => Nat.zero_le _) hu0)
      simp [hxu.symm]
    omega
  have hA : t2_cross (t3_G' G x y v u) S S ≤
      t2_cross (G.comap (Function.Embedding.subtype (· ∈ t3_R x y v))) S S +
      (∑ a ∈ S, ∑ b ∈ S, if (a : V) = u ∧ G.Adj v b then 1 else 0) +
      (∑ a ∈ S, ∑ b ∈ S, if (b : V) = u ∧ G.Adj a v then 1 else 0) := by
    simp only [t2_cross, ← sum_add_distrib]
    refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
    by_cases hab : (t3_G' G x y v u).Adj a b
    · rw [ite_eq_left hab]
      rw [t3_G', SimpleGraph.fromRel_adj] at hab
      rcases hab with ⟨-, (h | h) | (h | h)⟩
      · rw [ite_eq_left (show (G.comap (Function.Embedding.subtype (· ∈ t3_R x y v))).Adj a b
          from h)]; omega
      · rw [ite_eq_left h]; omega
      · rw [ite_eq_left (show (G.comap (Function.Embedding.subtype (· ∈ t3_R x y v))).Adj a b
          from h.symm)]; omega
      · rw [ite_eq_left (show (b : V) = u ∧ G.Adj a v from ⟨h.1, h.2.symm⟩)]; omega
    · rw [ite_eq_right hab]; omega
  have hne : ∀ a : t3_R x y v, a ≠ ⟨u, huR⟩ → (a : V) ≠ u := fun a ha h => ha (Subtype.ext h)
  have hB1 : (∑ a ∈ S, ∑ b ∈ S, if (a : V) = u ∧ G.Adj v b then 1 else 0) = N := by
    rw [sum_eq_single_of_mem _ hu0]
    · simp only [true_and, hN, G.adj_comm]
    · intro a _ ha
      exact sum_eq_zero fun b _ => ite_eq_right fun h => hne a ha h.1
  have hB2 : (∑ a ∈ S, ∑ b ∈ S, if (b : V) = u ∧ G.Adj a v then 1 else 0) = N := by
    rw [sum_comm, sum_eq_single_of_mem _ hu0]
    · simp only [true_and, hN]
    · intro b _ hb
      exact sum_eq_zero fun a _ => ite_eq_right fun h => hne b hb h.1
  rw [hcard] at hpT
  push_cast at hpT hpS
  omega

/-- **Claim 13.** If `xy` is an edge with `d(x) = d(y) = 3`, then `x` lies in a triangle. -/
theorem MinCounter.claim13 (hG : MinCounter G) {x y : V} (hxy : G.Adj x y)
    (hx : G.degree x = 3) (hy : G.degree y = 3) :
    ∃ a b, G.Adj x a ∧ G.Adj x b ∧ G.Adj a b := by
  by_contra hno
  push Not at hno
  obtain ⟨u, v, huv, huy, hvy, hxu, hxv, hNx⟩ := t3_nbr2 hx hxy
  obtain ⟨p, q, -, -, -, -, -, hNy⟩ := t3_nbr2 hy hxy.symm
  have hnuv : ¬ G.Adj u v := hno u v hxu hxv
  have hux : u ≠ x := (G.ne_of_adj hxu).symm
  have hvx : v ≠ x := (G.ne_of_adj hxv).symm
  have huR : u ∈ t3_R x y v := t3_mem.2 ⟨hux, huy, huv⟩
  by_cases hcol : (t3_G' G x y v u).Colorable 3
  · exact hG.crit.not_colorable (t3_extend hxu huv huy hnuv hNx hNy hcol)
  have hcard : Fintype.card (t3_R x y v) < Fintype.card V := by
    rw [Fintype.card_coe, ← card_univ]
    exact card_lt_card (ssubset_univ_iff.2 fun h => (t3_mem.1 (by rw [h]; exact mem_univ x)).1 rfl)
  obtain ⟨S, hSne, hSpot, hSnc⟩ := hG.small _ _ hcard hcol
  by_cases hu0 : (⟨u, huR⟩ : t3_R x y v) ∈ S
  · obtain ⟨T, hyT, hcT, hp⟩ := t3_pot hxu hxv hvx hvy (G.ne_of_adj hxy) huR S hu0
    have hS2 : 2 ≤ S.card := by
      by_contra h
      obtain ⟨a, rfl⟩ := card_eq_one.1 (show S.card = 1 by have := card_pos.2 hSne; omega)
      have h2 := t2_two_pot (t3_G' G x y v u) {a}
      have : t2_cross (t3_G' G x y v u) {a} {a} = 0 := by simp [t2_cross]
      rw [this, card_singleton] at h2
      omega
    have hT : T ≠ univ := fun h => hyT (by rw [h]; exact mem_univ y)
    have := hG.claim10 _ hT (by omega) (by omega)
    omega
  · apply hSnc
    obtain ⟨c⟩ := hG.crit.vertex x
    refine ⟨SimpleGraph.Coloring.mk (fun s => c ⟨s.1.1, (t3_mem.1 s.1.2).1⟩) ?_⟩
    intro s t hst
    apply c.valid
    show G.Adj s.1.1 t.1.1
    have hst' : (t3_G' G x y v u).Adj s.1 t.1 := hst
    rw [t3_G', SimpleGraph.fromRel_adj] at hst'
    have hsu : (s.1 : V) ≠ u := fun h => hu0 (by
      have : s.1 = ⟨u, huR⟩ := Subtype.ext h
      rw [← this]; exact s.2)
    have htu : (t.1 : V) ≠ u := fun h => hu0 (by
      have : t.1 = ⟨u, huR⟩ := Subtype.ext h
      rw [← this]; exact t.2)
    rcases hst' with ⟨-, (h | h) | (h | h)⟩
    · exact h
    · exact absurd h.1 hsu
    · exact h.symm
    · exact absurd h.1 htu

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
