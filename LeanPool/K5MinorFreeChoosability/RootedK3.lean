/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Minor

/-!
# Rooted `K_3` minors (Wood--Linusson, Lemmas 4 and 5)

All graphs here live on a fixed vertex type `V`; the graph under consideration is the
subgraph of `G` induced on a finite vertex set `S` (edges leaving `S` are ignored).

A `K_3` minor rooted at `x, y, z` consists of three pairwise disjoint, pairwise adjacent,
connected branch sets inside `S` containing `x`, `y`, `z` respectively.  A vertex `u` is
*good* if two of the roots different from `u` are joined by a path avoiding `u`.

* `RootedK3.good`: every vertex is good if there is a rooted `K_3` minor
  (Lemma 5, `⇒`).
* `rootedK3_of_good`: if every vertex is good there is a rooted `K_3` minor
  (Lemma 5, `⇐`).  Its proof follows Wood--Linusson: induction on `|S|`, deleting a vertex
  outside the component of the roots, contracting an edge at a cut vertex, and in the
  2-connected case contracting an edge given by `exists_contractible_edge`, our rooted
  version of Lemma 4 (proved by the same minimal-component argument).
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V]

/-- A `K_3` minor of `G[S]` rooted at `x, y, z`. -/
def RootedK3 (G : SimpleGraph V) (S : Finset V) (x y z : V) : Prop :=
  ∃ X Y Z : Finset V, X ⊆ S ∧ Y ⊆ S ∧ Z ⊆ S ∧ x ∈ X ∧ y ∈ Y ∧ z ∈ Z ∧
    ConnSet G ↑X ∧ ConnSet G ↑Y ∧ ConnSet G ↑Z ∧
    Disjoint X Y ∧ Disjoint Y Z ∧ Disjoint X Z ∧
    (∃ a ∈ X, ∃ b ∈ Y, G.Adj a b) ∧ (∃ a ∈ Y, ∃ b ∈ Z, G.Adj a b) ∧
    (∃ a ∈ X, ∃ b ∈ Z, G.Adj a b)

/-- The vertex `u` is good with respect to the roots `x, y, z` in `G[S]`: two different
roots other than `u` lie in the same component of `G[S] - u`. -/
def Good (G : SimpleGraph V) (S : Finset V) (x y z u : V) : Prop :=
  ∃ a ∈ ({x, y, z} : Finset V), ∃ b ∈ ({x, y, z} : Finset V),
    a ≠ b ∧ a ≠ u ∧ b ≠ u ∧ RIn G ↑(S.erase u) a b

/-- Contraction of the edge `vw` into `w`: the vertex `v` disappears and `w` inherits its
neighbours. -/
def contract (G : SimpleGraph V) (v w : V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ a ≠ v ∧ b ≠ v ∧ (G.Adj a b ∨ (a = w ∧ G.Adj v b) ∨ (b = w ∧ G.Adj v a))
  symm := ⟨fun _ _ ⟨h1, h2, h3, h4⟩ => ⟨h1.symm, h3, h2, by
    rcases h4 with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

section Contract

variable {G : SimpleGraph V} {v w : V}

omit [DecidableEq V] in
theorem contract_adj_of_adj {a b : V} (h : G.Adj a b) (ha : a ≠ v) (hb : b ≠ v) :
    (contract G v w).Adj a b :=
  ⟨G.ne_of_adj h, ha, hb, Or.inl h⟩

/-- Reachability is preserved by the contraction, mapping `v` to `w`. -/
theorem RIn.contract {s t : Set V} {a b : V} (hvw : G.Adj v w) (h : RIn G s a b)
    (hst : ∀ c ∈ s, (if c = v then w else c) ∈ t) :
    RIn (contract G v w) t (if a = v then w else a) (if b = v then w else b) := by
  refine h.map (fun c => if c = v then w else c) (fun p q hpq hp hq => ?_)
  have hwv : w ≠ v := (G.ne_of_adj hvw).symm
  have hp' := hst p hp
  have hq' := hst q hq
  by_cases hpv : p = v <;> by_cases hqv : q = v
  · subst hpv; subst hqv; exact absurd hpq (G.irrefl)
  · subst hpv
    simp only [↓reduceIte, hqv] at hp' hq' ⊢
    by_cases hqw : q = w
    · subst hqw; exact RIn.refl _
    · exact RIn.single ⟨Ne.symm hqw, hwv, hqv, Or.inr (Or.inl ⟨rfl, hpq⟩)⟩ hp' hq'
  · subst hqv
    simp only [↓reduceIte, hpv] at hp' hq' ⊢
    by_cases hpw : p = w
    · subst hpw; exact RIn.refl _
    · exact RIn.single ⟨hpw, hpv, hwv, Or.inr (Or.inr ⟨rfl, hpq.symm⟩)⟩ hp' hq'
  · simp only [hpv, hqv, ↓reduceIte] at hp' hq' ⊢
    exact RIn.single (contract_adj_of_adj hpq hpv hqv) hp' hq'

/-- The branch set of the uncontracted graph corresponding to a branch set `X`. -/
def liftSet (v w : V) (X : Finset V) : Finset V := if w ∈ X then insert v X else X

theorem subset_liftSet (X : Finset V) : X ⊆ liftSet v w X := by
  unfold liftSet; split_ifs
  · exact Finset.subset_insert _ _
  · exact subset_rfl

theorem liftSet_subset {X S : Finset V} (hX : X ⊆ S.erase v) (hv : v ∈ S) :
    liftSet v w X ⊆ S := by
  unfold liftSet; split_ifs
  · exact Finset.insert_subset hv (hX.trans (Finset.erase_subset _ _))
  · exact hX.trans (Finset.erase_subset _ _)

theorem connSet_liftSet (hvw : G.Adj v w) {X : Finset V}
    (hX : ConnSet (contract G v w) ↑X) : ConnSet G ↑(liftSet v w X) := by
  have hsub : (↑X : Set V) ⊆ ↑(liftSet v w X) := by exact_mod_cast subset_liftSet X
  have hin : ∀ a ∈ X, ∀ b ∈ X, RIn G ↑(liftSet v w X) a b := by
    intro a ha b hb
    refine ((hX.2 a ha b hb).map id (fun p q hpq hp hq => ?_))
    obtain ⟨_, _, _, h | ⟨hpw, h⟩ | ⟨hqw, h⟩⟩ := hpq
    · exact RIn.single h (hsub hp) (hsub hq)
    · subst hpw
      have hvl : v ∈ liftSet v p X := by simp [liftSet, Finset.mem_coe.1 hp]
      exact RIn.head hvw.symm (hsub hp) hvl (RIn.single h hvl (hsub hq))
    · subst hqw
      have hvl : v ∈ liftSet v q X := by simp [liftSet, Finset.mem_coe.1 hq]
      exact RIn.head h.symm (hsub hp) hvl (RIn.single hvw hvl (hsub hq))
  have hto : ∀ a ∈ liftSet v w X, ∃ a' ∈ X, RIn G ↑(liftSet v w X) a a' := by
    intro a ha
    unfold liftSet at ha
    split_ifs at ha with hw
    · rcases Finset.mem_insert.1 ha with hav | ha
      · subst hav
        have hvl : a ∈ liftSet a w X := by simp [liftSet, hw]
        exact ⟨w, hw, RIn.single hvw hvl (hsub hw)⟩
      · exact ⟨a, ha, RIn.refl _⟩
    · exact ⟨a, ha, RIn.refl _⟩
  obtain ⟨x, hx⟩ := hX.1
  refine ⟨⟨x, hsub hx⟩, fun a ha b hb => ?_⟩
  obtain ⟨a', ha', haa⟩ := hto a ha
  obtain ⟨b', hb', hbb⟩ := hto b hb
  exact (haa.trans (hin a' ha' b' hb')).trans hbb.symm

theorem disjoint_liftSet {S X Y : Finset V} (hX : X ⊆ S.erase v) (hY : Y ⊆ S.erase v)
    (h : Disjoint X Y) : Disjoint (liftSet v w X) (liftSet v w Y) := by
  have hvX : v ∉ X := fun hv => by simpa using hX hv
  have hvY : v ∉ Y := fun hv => by simpa using hY hv
  unfold liftSet
  split_ifs with h1 h2 h2
  · exact absurd h2 (Finset.disjoint_left.1 h h1)
  · simpa [hvY] using h
  · simpa [hvX] using h
  · exact h

theorem adj_liftSet (hvw : G.Adj v w) {X Y : Finset V} {a b : V} (ha : a ∈ X) (hb : b ∈ Y)
    (hab : (contract G v w).Adj a b) :
    ∃ a' ∈ liftSet v w X, ∃ b' ∈ liftSet v w Y, G.Adj a' b' := by
  obtain ⟨_, _, _, h | ⟨haw, h⟩ | ⟨hbw, h⟩⟩ := hab
  · exact ⟨a, subset_liftSet X ha, b, subset_liftSet Y hb, h⟩
  · subst haw
    exact ⟨v, by simp [liftSet, ha], b, subset_liftSet Y hb, h⟩
  · subst hbw
    exact ⟨a, subset_liftSet X ha, v, by simp [liftSet, hb], h.symm⟩

/-- A rooted `K_3` minor of the contraction lifts to the original graph. -/
theorem RootedK3.of_contract {S : Finset V} {x y z : V} (hv : v ∈ S) (hvw : G.Adj v w)
    (h : RootedK3 (contract G v w) (S.erase v) x y z) : RootedK3 G S x y z := by
  obtain ⟨X, Y, Z, hXS, hYS, hZS, hx, hy, hz, hcX, hcY, hcZ, hXY, hYZ, hXZ,
    ⟨a1, ha1, b1, hb1, h1⟩, ⟨a2, ha2, b2, hb2, h2⟩, ⟨a3, ha3, b3, hb3, h3⟩⟩ := h
  exact ⟨liftSet v w X, liftSet v w Y, liftSet v w Z, liftSet_subset hXS hv,
    liftSet_subset hYS hv, liftSet_subset hZS hv, subset_liftSet X hx, subset_liftSet Y hy,
    subset_liftSet Z hz, connSet_liftSet hvw hcX, connSet_liftSet hvw hcY,
    connSet_liftSet hvw hcZ, disjoint_liftSet hXS hYS hXY, disjoint_liftSet hYS hZS hYZ,
    disjoint_liftSet hXS hZS hXZ, adj_liftSet hvw ha1 hb1 h1, adj_liftSet hvw ha2 hb2 h2,
    adj_liftSet hvw ha3 hb3 h3⟩

end Contract

omit [DecidableEq V] in
theorem RootedK3.mono {G : SimpleGraph V} {S S' : Finset V} {x y z : V}
    (h : RootedK3 G S x y z) (hS : S ⊆ S') : RootedK3 G S' x y z := by
  obtain ⟨X, Y, Z, hXS, hYS, hZS, rest⟩ := h
  exact ⟨X, Y, Z, hXS.trans hS, hYS.trans hS, hZS.trans hS, rest⟩

section Lemma4

variable {G : SimpleGraph V} {S R : Finset V} {v : V}

/-- **Rooted form of Wood--Linusson, Lemma 4.**  In a 2-connected graph `G[S]`, a vertex
`v` outside the root set `R` (which has at least three elements) is incident to an edge
`vw` such that two roots different from `w` remain connected after deleting `v` and `w`;
equivalently, the vertex obtained by contracting `vw` is good. -/
theorem exists_contractible_edge
    (h2 : ∀ c ∈ S, ∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ c → t₂ ≠ c → RIn G ↑(S.erase c) t₁ t₂)
    (hv : v ∈ S) (hvR : v ∉ R) (hRS : R ⊆ S)
    (hR3 : ∀ w, ∃ r₁ ∈ R, ∃ r₂ ∈ R, r₁ ≠ r₂ ∧ r₁ ≠ w ∧ r₂ ≠ w) :
    ∃ w ∈ S, G.Adj v w ∧ ∃ r₁ ∈ R, ∃ r₂ ∈ R, r₁ ≠ r₂ ∧ r₁ ≠ w ∧ r₂ ≠ w ∧
      RIn G (↑S \ {v, w}) r₁ r₂ := by
  classical
  by_contra hno
  push Not at hno
  -- a first neighbour of `v`
  obtain ⟨a₁, ha₁, a₂, ha₂, ha₁₂, ha₁v, ha₂v⟩ := hR3 v
  have hva₁ : RIn G ↑S v a₁ :=
    (h2 a₂ (hRS ha₂) v hv a₁ (hRS ha₁) (fun h => ha₂v h.symm) ha₁₂).mono_set
      (Finset.coe_subset.2 (Finset.erase_subset _ _))
  obtain ⟨p, q, _, hpS, hpP, hqS, hqP, hpq⟩ :=
    hva₁.exit (P := {v}) rfl (by simpa using ha₁v)
  simp only [Set.mem_singleton_iff] at hpP hqP
  subst hpP
  -- components
  let comp : V → V → Finset V := fun w r =>
    S.filter (fun t => t ≠ p ∧ t ≠ w ∧ RIn G (↑S \ {p, w}) r t)
  have claim : ∀ n, ∀ w r, w ∈ S → G.Adj p w → r ∈ R → r ≠ w → (comp w r).card = n →
      False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro w r hwS hpw hrR hrw hcard
    have hrp : r ≠ p := fun h => hvR (h ▸ hrR)
    have hwp : w ≠ p := (G.ne_of_adj hpw).symm
    have hmemH : ∀ t, t ∈ comp w r ↔ t ∈ S ∧ t ≠ p ∧ t ≠ w ∧ RIn G (↑S \ {p, w}) r t := by
      intro t; simp [comp]
    -- (i) a neighbour `x` of `p` in the component
    have hrv : RIn G ↑(S.erase w) r p := h2 w hwS r (hRS hrR) p hv hrw hwp.symm
    obtain ⟨x, q', _, hxS, hxH, hq'S, hq'H, hxq'⟩ :=
      hrv.exit (P := ↑(comp w r)) (by simpa [hmemH] using
        ⟨hRS hrR, hrp, hrw, RIn.refl _⟩) (by simp [hmemH])
    rw [Finset.mem_coe, hmemH] at hxH
    obtain ⟨hxS', hxp, hxw, hrx⟩ := hxH
    have hq'p : q' = p := by
      by_contra hne
      apply hq'H
      rw [Finset.mem_coe, hmemH]
      simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
        at hq'S
      refine ⟨hq'S.1, hne, hq'S.2, hrx.tail hxq' ?_ ?_⟩
      · simp [hxS', hxp, hxw]
      · simp [hq'S.1, hne, hq'S.2]
    subst hq'p
    have hpx : G.Adj q' x := hxq'.symm
    -- (ii) everything outside the component reaches `w` avoiding `q'` and `x`
    have hout : ∀ t ∈ S, t ≠ q' → t ∉ comp w r → RIn G (↑S \ {q', x}) t w := by
      intro t htS htp htH
      by_cases htw : t = w
      · subst htw; exact RIn.refl _
      have htw' : RIn G ↑(S.erase q') t w := h2 q' hv t htS w hwS htp hwp
      obtain ⟨a, b, hta, _, haP, hbS, hbP, hab⟩ :=
        htw'.exit (P := {t' | t' ∈ S ∧ t' ≠ q' ∧ t' ≠ w ∧ t' ∉ comp w r})
          ⟨htS, htp, htw, htH⟩ (by simp)
      obtain ⟨haS, hap, haw, haH⟩ := haP
      simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
        at hbS
      have hbw : b = w := by
        by_contra hbw
        have hbH : b ∈ comp w r := by
          by_contra hbH
          exact hbP ⟨hbS.1, hbS.2, hbw, hbH⟩
        apply haH
        rw [hmemH] at hbH ⊢
        refine ⟨haS, hap, haw, hbH.2.2.2.tail hab.symm ?_ ?_⟩
        · simp [hbS.1, hbS.2, hbw]
        · simp [haS, hap, haw]
      subst hbw
      have hax : a ≠ x := by
        rintro rfl
        apply haH
        rw [hmemH]
        exact ⟨hxS', hxp, hxw, hrx⟩
      refine (hta.mono_set ?_).tail hab ?_ ?_
      · intro c hc
        simp only [Set.mem_inter_iff, Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe,
          Set.mem_singleton_iff, Set.mem_ofPred_eq] at hc
        refine ⟨hc.1.1, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        refine ⟨hc.1.2, ?_⟩
        rintro rfl
        exact hc.2.2.2.2 ((hmemH c).2 ⟨hxS', hxp, hxw, hrx⟩)
      · simp [haS, hap, hax]
      · simp only [Set.mem_sdiff, SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or]
        exact ⟨hbS.1, hwp, fun h => hxw h.symm⟩
    -- (iii) a root separated from `w` by `{q', x}`
    obtain ⟨b₁, hb₁, b₂, hb₂, hb₁₂, hb₁x, hb₂x⟩ := hR3 x
    have hsep := hno x hxS' hpx
    have hr' : ∃ r' ∈ R, r' ≠ x ∧ ¬ RIn G (↑S \ {q', x}) r' w := by
      by_cases h₁ : RIn G (↑S \ {q', x}) b₁ w
      · by_cases h₂ : RIn G (↑S \ {q', x}) b₂ w
        · exact absurd (h₁.trans h₂.symm) (hsep b₁ hb₁ b₂ hb₂ hb₁₂ hb₁x hb₂x)
        · exact ⟨b₂, hb₂, hb₂x, h₂⟩
      · exact ⟨b₁, hb₁, hb₁x, h₁⟩
    obtain ⟨r', hr'R, hr'x, hr'w⟩ := hr'
    have hr'p : r' ≠ q' := fun h => hvR (h ▸ hr'R)
    have hr'H : r' ∈ comp w r := by
      by_contra h
      exact hr'w (hout r' (hRS hr'R) hr'p h)
    -- (iv) the new component is strictly smaller
    have hsub : comp x r' ⊆ (comp w r).erase x := by
      intro t ht
      simp only [comp, Finset.mem_filter] at ht
      obtain ⟨htS, htp, htx, hrt⟩ := ht
      refine Finset.mem_erase.2 ⟨htx, ?_⟩
      by_contra htH
      exact hr'w (hrt.trans (hout t htS htp htH))
    have hlt : (comp x r').card < n := by
      have hxH : x ∈ comp w r := (hmemH x).2 ⟨hxS', hxp, hxw, hrx⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hxH] at this
      have : 0 < (comp w r).card := Finset.card_pos.2 ⟨x, hxH⟩
      omega
    exact ih _ hlt x r' hxS' hpx hr'R hr'x rfl
  obtain ⟨r, hr, -, -, -, hrq, -⟩ := hR3 q
  exact claim _ q r hqS hpq hr hrq rfl

end Lemma4

end LeanPool.K5MinorFreeChoosability
