/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.RootedK3

/-!
# Wood--Linusson, Lemma 5: rooted `K_3` minors

`rootedK3_iff_good`: for distinct roots `x, y, z` of `G[S]`, there is a `K_3` minor rooted
at `x, y, z` if and only if every vertex of `S` is good.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {S : Finset V} {x y z : V}

theorem good_comm₁₂ {u : V} : Good G S x y z u ↔ Good G S y x z u := by
  unfold Good; rw [Finset.insert_comm]

theorem good_comm₂₃ {u : V} : Good G S x y z u ↔ Good G S x z y u := by
  unfold Good; rw [Finset.pair_comm]

theorem rIn_of_good_root (h : Good G S x y z x) : RIn G ↑(S.erase x) y z := by
  obtain ⟨a, ha, b, hb, hab, hax, hbx, hr⟩ := h
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | exact absurd rfl hab | exact absurd rfl hax | exact absurd rfl hbx | exact hr |
      exact hr.symm

theorem mem_roots_cases {r : V} (hr : r ∈ ({x, y, z} : Finset V)) : r = x ∨ r = y ∨ r = z := by
  simpa using hr

/-- Goodness of the vertices of a contraction `G / dk` (keeping `k`), given goodness in `G`
of the other vertices and a pair of roots joined avoiding `d` and `k`. -/
theorem good_contract {d k : V} (hk : k ∈ S) (hdk : G.Adj d k)
    (hdR : d ∉ ({x, y, z} : Finset V))
    (hgood : ∀ u ∈ S, u ≠ d → u ≠ k → Good G S x y z u)
    {r₁ r₂ : V} (hr₁ : r₁ ∈ ({x, y, z} : Finset V)) (hr₂ : r₂ ∈ ({x, y, z} : Finset V))
    (hr₁₂ : r₁ ≠ r₂) (hr₁k : r₁ ≠ k) (hr₂k : r₂ ≠ k)
    (hr : RIn G (↑S \ {d, k}) r₁ r₂) :
    ∀ u ∈ S.erase d, Good (contract G d k) (S.erase d) x y z u := by
  have hkd : k ≠ d := (G.ne_of_adj hdk).symm
  have hRd : ∀ r ∈ ({x, y, z} : Finset V), r ≠ d := fun r hr h => hdR (h ▸ hr)
  intro u hu
  have hud : u ≠ d := Finset.ne_of_mem_erase hu
  have huS : u ∈ S := Finset.mem_of_mem_erase hu
  by_cases huk : u = k
  · subst huk
    refine ⟨r₁, hr₁, r₂, hr₂, hr₁₂, hr₁k, hr₂k, ?_⟩
    have := hr.contract (t := ↑((S.erase d).erase u)) hdk (fun c hc => ?_)
    · simpa [hRd r₁ hr₁, hRd r₂ hr₂] using this
    · simp only [Set.mem_sdiff, Finset.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff,
        not_or] at hc
      simp [hc.2.1, hc.1, hc.2.2]
  · obtain ⟨a, ha, b, hb, hab, hau, hbu, hr'⟩ := hgood u huS hud huk
    refine ⟨a, ha, b, hb, hab, hau, hbu, ?_⟩
    have := hr'.contract (t := ↑((S.erase d).erase u)) hdk (fun c hc => ?_)
    · simpa [hRd a ha, hRd b hb] using this
    · simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at hc
      by_cases hcd : c = d
      · simp [hcd, hkd, hk, Ne.symm huk]
      · simp [hcd, hc.1, hc.2]

/-- **Wood--Linusson, Lemma 5 (`⇐`).**  If every vertex of `G[S]` is good with respect to
the distinct roots `x, y, z ∈ S`, then `G[S]` has a `K_3` minor rooted at `x, y, z`. -/
theorem rootedK3_of_good (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : x ≠ z) (hgood : ∀ u ∈ S, Good G S x y z u) : RootedK3 G S x y z := by
  suffices h : ∀ n (G : SimpleGraph V) (S : Finset V), S.card = n → x ∈ S → y ∈ S → z ∈ S →
      (∀ u ∈ S, Good G S x y z u) → RootedK3 G S x y z from h _ G S rfl hx hy hz hgood
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G S hn hx hy hz hgood
  have hsubS : ∀ c, (↑(S.erase c) : Set V) ⊆ ↑S := fun c =>
    Finset.coe_subset.2 (Finset.erase_subset _ _)
  have hyz' : RIn G ↑S y z := (rIn_of_good_root (hgood x hx)).mono_set (hsubS x)
  have hxz' : RIn G ↑S x z :=
    (rIn_of_good_root (good_comm₁₂.1 (hgood y hy))).mono_set (hsubS y)
  have hxy' : RIn G ↑S x y :=
    (rIn_of_good_root (good_comm₁₂.1 (good_comm₂₃.1 (hgood z hz)))).mono_set (hsubS z)
  have hxR : ∀ r ∈ ({x, y, z} : Finset V), RIn G ↑S x r := by
    intro r hr
    rcases mem_roots_cases hr with rfl | rfl | rfl
    · exact RIn.refl _
    · exact hxy'
    · exact hxz'
  have hRS : ({x, y, z} : Finset V) ⊆ S := by
    intro r hr
    rcases mem_roots_cases hr with rfl | rfl | rfl <;> assumption
  have hRcard : ({x, y, z} : Finset V).card = 3 :=
    Finset.card_eq_three.2 ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  -- the generic contraction step
  have step : ∀ d k, d ∈ S → k ∈ S → G.Adj d k → d ∉ ({x, y, z} : Finset V) →
      (∀ u ∈ S, u ≠ d → u ≠ k → Good G S x y z u) →
      ∀ r₁ ∈ ({x, y, z} : Finset V), ∀ r₂ ∈ ({x, y, z} : Finset V), r₁ ≠ r₂ → r₁ ≠ k →
      r₂ ≠ k → RIn G (↑S \ {d, k}) r₁ r₂ → RootedK3 G S x y z := by
    intro d k hd hk hdk hdR hg r₁ hr₁ r₂ hr₂ hr₁₂ hr₁k hr₂k hr
    have hRd : ∀ r ∈ ({x, y, z} : Finset V), r ≠ d := fun r hr h => hdR (h ▸ hr)
    have hcard : (S.erase d).card < n := by
      rw [Finset.card_erase_of_mem hd, ← hn]
      exact Nat.sub_lt (Finset.card_pos.2 ⟨d, hd⟩) one_pos
    refine RootedK3.of_contract hd hdk (ih _ hcard (contract G d k) (S.erase d) rfl ?_ ?_ ?_
      (good_contract hk hdk hdR hg hr₁ hr₂ hr₁₂ hr₁k hr₂k hr))
    · exact Finset.mem_erase.2 ⟨hRd x (by simp), hx⟩
    · exact Finset.mem_erase.2 ⟨hRd y (by simp), hy⟩
    · exact Finset.mem_erase.2 ⟨hRd z (by simp), hz⟩
  by_cases hsmall : S.card ≤ 3
  · -- base case: `S = {x, y, z}` and goodness forces a triangle
    have hSR : ({x, y, z} : Finset V) = S :=
      Finset.eq_of_subset_of_card_le hRS (by rw [hRcard]; exact hsmall)
    have hpair : ∀ a b c, ({x, y, z} : Finset V) = {a, b, c} → a ≠ b → a ≠ c → b ≠ c →
        RIn G ↑(S.erase c) a b → G.Adj a b := by
      intro a b c habc hab hac hbc h
      refine RIn.adj_of_pair (h.mono_set ?_) hab
      intro t ht
      rw [← hSR, habc] at ht
      simp only [Finset.coe_erase, Finset.coe_insert, Finset.coe_singleton, Set.mem_sdiff,
        Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have h12 : G.Adj x y := hpair x y z rfl hxy hxz hyz
      (rIn_of_good_root (good_comm₁₂.1 (good_comm₂₃.1 (hgood z hz))))
    have h23 : G.Adj y z := hpair y z x (by rw [Finset.insert_comm, Finset.pair_comm,
      Finset.insert_comm]) hyz (Ne.symm hxy) (Ne.symm hxz) (rIn_of_good_root (hgood x hx))
    have h13 : G.Adj x z := hpair x z y (by rw [Finset.pair_comm]) hxz hxy (Ne.symm hyz)
      (rIn_of_good_root (good_comm₁₂.1 (hgood y hy)))
    refine ⟨{x}, {y}, {z}, by simpa using hx, by simpa using hy, by simpa using hz,
      by simp, by simp, by simp, by simpa using connSet_singleton G x,
      by simpa using connSet_singleton G y, by simpa using connSet_singleton G z,
      by simpa using hxy, by simpa using hyz, by simpa using hxz,
      ⟨x, by simp, y, by simp, h12⟩, ⟨y, by simp, z, by simp, h23⟩,
      ⟨x, by simp, z, by simp, h13⟩⟩
  push Not at hsmall
  by_cases hD : ∃ t ∈ S, ¬ RIn G ↑S x t
  · -- disconnected: delete a vertex outside the component of the roots
    obtain ⟨t, htS, htx⟩ := hD
    have htR : t ∉ ({x, y, z} : Finset V) := fun h => htx (hxR t h)
    have hcard : (S.erase t).card < n := by
      rw [Finset.card_erase_of_mem htS, ← hn]
      exact Nat.sub_lt (Finset.card_pos.2 ⟨t, htS⟩) one_pos
    have hne : ∀ r ∈ ({x, y, z} : Finset V), r ≠ t := fun r hr h => htR (h ▸ hr)
    refine (ih _ hcard G (S.erase t) rfl (Finset.mem_erase.2 ⟨hne x (by simp), hx⟩)
      (Finset.mem_erase.2 ⟨hne y (by simp), hy⟩) (Finset.mem_erase.2 ⟨hne z (by simp), hz⟩)
      (fun u hu => ?_)).mono (Finset.erase_subset _ _)
    obtain ⟨a, ha, b, hb, hab, hau, hbu, hr⟩ := hgood u (Finset.mem_of_mem_erase hu)
    refine ⟨a, ha, b, hb, hab, hau, hbu, ?_⟩
    have hat : ¬ RIn G ↑(S.erase u) a t := fun h =>
      htx ((hxR a ha).trans (h.mono_set (hsubS u)))
    refine (hr.avoid hat).mono_set ?_
    intro c hc
    simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at hc ⊢
    exact ⟨⟨hc.1.1, hc.2⟩, hc.1.2⟩
  push Not at hD
  by_cases hC : ∃ c ∈ S, ∃ t₁ ∈ S, ∃ t₂ ∈ S, t₁ ≠ c ∧ t₂ ≠ c ∧ ¬ RIn G ↑(S.erase c) t₁ t₂
  · -- a cut vertex `c`: contract an edge from `c` into a component avoiding two roots
    obtain ⟨c, hcS, t₁, ht₁, t₂, ht₂, ht₁c, ht₂c, hsep⟩ := hC
    obtain ⟨r₁, hr₁, r₂, hr₂, hr₁₂, hr₁c, hr₂c, hr⟩ := hgood c hcS
    have ht : ∃ t ∈ S, t ≠ c ∧ ¬ RIn G ↑(S.erase c) r₁ t := by
      by_cases h₁ : RIn G ↑(S.erase c) r₁ t₁
      · refine ⟨t₂, ht₂, ht₂c, fun h₂ => hsep (h₁.symm.trans h₂)⟩
      · exact ⟨t₁, ht₁, ht₁c, h₁⟩
    obtain ⟨t, htS, htc, htr⟩ := ht
    have htr₁ : RIn G ↑S t r₁ := (hD t htS).symm.trans (hxR r₁ hr₁)
    obtain ⟨w, q, _, hwS, hwP, hqS, hqP, hwq⟩ :=
      htr₁.exit (P := {s | s ≠ c ∧ ¬ RIn G ↑(S.erase c) r₁ s}) ⟨htc, htr⟩
        (fun h => h.2 (RIn.refl _))
    obtain ⟨hwc, hwr⟩ := hwP
    have hqc : q = c := by
      by_contra hqc
      apply hwr
      have hq : RIn G ↑(S.erase c) r₁ q := by
        by_contra h
        exact hqP ⟨hqc, h⟩
      exact hq.tail hwq.symm (by simp [hqc, Finset.mem_coe.1 hqS])
        (by simp [hwc, Finset.mem_coe.1 hwS])
    subst hqc
    have hwr₁ : w ≠ r₁ := fun h => hwr (h ▸ RIn.refl _)
    have hwr₂ : w ≠ r₂ := fun h => hwr (h ▸ hr)
    have hr' : RIn G (↑S \ {q, w}) r₁ r₂ := by
      refine (hr.avoid hwr).mono_set ?_
      intro s hs
      simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff] at hs
      simp [hs.1.1, hs.1.2, hs.2]
    by_cases hwR : w ∈ ({x, y, z} : Finset V)
    · have hqR : q ∉ ({x, y, z} : Finset V) := by
        intro hqR
        have hsub : ({r₁, r₂, w, q} : Finset V) ⊆ {x, y, z} := by
          intro s hs
          simp only [Finset.mem_insert, Finset.mem_singleton] at hs
          rcases hs with rfl | rfl | rfl | rfl <;> assumption
        have h4 : ({r₁, r₂, w, q} : Finset V).card = 4 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hwc]
          · simp [Ne.symm hwr₂, hr₂c]
          · simp [hr₁₂, Ne.symm hwr₁, hr₁c]
        have := Finset.card_le_card hsub
        omega
      refine step q w (Finset.mem_coe.1 hqS) (Finset.mem_coe.1 hwS) hwq.symm hqR
        (fun u hu huq huw => hgood u hu) r₁ hr₁ r₂ hr₂ hr₁₂ (Ne.symm hwr₁) (Ne.symm hwr₂) hr'
    · refine step w q (Finset.mem_coe.1 hwS) (Finset.mem_coe.1 hqS) hwq hwR
        (fun u hu huq huw => hgood u hu) r₁ hr₁ r₂ hr₂ hr₁₂ hr₁c hr₂c ?_
      refine hr'.mono_set ?_
      intro s hs
      simp only [Set.mem_sdiff, Finset.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff,
        not_or] at hs ⊢
      exact ⟨hs.1, hs.2.2, hs.2.1⟩
  · -- 2-connected: contract an edge given by the rooted Lemma 4
    push Not at hC
    obtain ⟨v, hvS, hvR⟩ := Finset.exists_mem_notMem_of_card_lt_card (by omega :
      ({x, y, z} : Finset V).card < S.card)
    have hR3 : ∀ w, ∃ r₁ ∈ ({x, y, z} : Finset V), ∃ r₂ ∈ ({x, y, z} : Finset V),
        r₁ ≠ r₂ ∧ r₁ ≠ w ∧ r₂ ≠ w := by
      intro w
      by_cases hwx : w = x
      · subst hwx; exact ⟨y, by simp, z, by simp, hyz, Ne.symm hxy, Ne.symm hxz⟩
      by_cases hwy : w = y
      · subst hwy; exact ⟨x, by simp, z, by simp, hxz, hxy, Ne.symm hyz⟩
      · exact ⟨x, by simp, y, by simp, hxy, Ne.symm hwx, Ne.symm hwy⟩
    obtain ⟨w, hwS, hvw, r₁, hr₁, r₂, hr₂, hr₁₂, hr₁w, hr₂w, hr⟩ :=
      exists_contractible_edge (fun c hc t₁ ht₁ t₂ ht₂ h₁ h₂ => hC c hc t₁ ht₁ t₂ ht₂ h₁ h₂)
        hvS hvR hRS hR3
    exact step v w hvS hwS hvw hvR (fun u hu _ _ => hgood u hu) r₁ hr₁ r₂ hr₂ hr₁₂ hr₁w hr₂w hr

/-- **Wood--Linusson, Lemma 5 (`⇒`).**  If `G[S]` has a `K_3` minor rooted at `x, y, z`,
every vertex of `S` is good. -/
theorem RootedK3.good (h : RootedK3 G S x y z) : ∀ u ∈ S, Good G S x y z u := by
  obtain ⟨X, Y, Z, hXS, hYS, hZS, hx, hy, hz, hcX, hcY, hcZ, hXY, hYZ, hXZ,
    ⟨a1, ha1, b1, hb1, h1⟩, ⟨a2, ha2, b2, hb2, h2⟩, ⟨a3, ha3, b3, hb3, h3⟩⟩ := h
  intro u _
  -- connect two roots through the union of two branch sets avoiding `u`
  have hpair : ∀ (P Q : Finset V) (p q a b : V), P ⊆ S → Q ⊆ S → p ∈ P → q ∈ Q →
      ConnSet G ↑P → ConnSet G ↑Q → a ∈ P → b ∈ Q → G.Adj a b → u ∉ P → u ∉ Q →
      RIn G ↑(S.erase u) p q := by
    intro P Q p q a b hPS hQS hp hq hcP hcQ ha hb hab huP huQ
    have hP' : (↑P : Set V) ⊆ ↑(S.erase u) := by
      intro t ht
      simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
      exact ⟨hPS ht, fun h => huP (h ▸ ht)⟩
    have hQ' : (↑Q : Set V) ⊆ ↑(S.erase u) := by
      intro t ht
      simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
      exact ⟨hQS ht, fun h => huQ (h ▸ ht)⟩
    exact (((hcP.2 p hp a ha).mono_set hP').tail hab (hP' ha) (hQ' hb)).trans
      ((hcQ.2 b hb q hq).mono_set hQ')
  have hxy : x ≠ y := fun h => Finset.disjoint_left.1 hXY hx (h ▸ hy)
  have hyz : y ≠ z := fun h => Finset.disjoint_left.1 hYZ hy (h ▸ hz)
  have hxz : x ≠ z := fun h => Finset.disjoint_left.1 hXZ hx (h ▸ hz)
  by_cases huX : u ∈ X
  · have huY : u ∉ Y := fun h => Finset.disjoint_left.1 hXY huX h
    have huZ : u ∉ Z := fun h => Finset.disjoint_left.1 hXZ huX h
    exact ⟨y, by simp, z, by simp, hyz, fun h => huY (h ▸ hy), fun h => huZ (h ▸ hz),
      hpair Y Z y z a2 b2 hYS hZS hy hz hcY hcZ ha2 hb2 h2 huY huZ⟩
  · by_cases huY : u ∈ Y
    · have huZ : u ∉ Z := fun h => Finset.disjoint_left.1 hYZ huY h
      exact ⟨x, by simp, z, by simp, hxz, fun h => huX (h ▸ hx), fun h => huZ (h ▸ hz),
        hpair X Z x z a3 b3 hXS hZS hx hz hcX hcZ ha3 hb3 h3 huX huZ⟩
    · exact ⟨x, by simp, y, by simp, hxy, fun h => huX (h ▸ hx), fun h => huY (h ▸ hy),
        hpair X Y x y a1 b1 hXS hYS hx hy hcX hcY ha1 hb1 h1 huX huY⟩

/-- **Wood--Linusson, Lemma 5.**  For distinct `x, y, z ∈ S`, `G[S]` has a `K_3` minor
rooted at `x, y, z` if and only if every vertex of `S` is good. -/
theorem rootedK3_iff_good (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : x ≠ z) : RootedK3 G S x y z ↔ ∀ u ∈ S, Good G S x y z u :=
  ⟨RootedK3.good, rootedK3_of_good hx hy hz hxy hyz hxz⟩

end LeanPool.K5MinorFreeChoosability
