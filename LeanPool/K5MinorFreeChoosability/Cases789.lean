/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Cases

/-!
# Cases 7--9 of Wood--Linusson, Lemma 7

* `case7`: once Cases 4--6 do not apply, no vertex of `B` has three neighbours in `B`
  (otherwise Lemma 5 yields a rooted `K_3` minor and hence a `K_5` minor of `G^{B+α}`);
* `case8`: `G[A]` is a component of `G[B]`: delete a vertex of `A`;
* `case9`: delete a vertex `v ∈ B \ A` adjacent to `A`, reserving two colours for it.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V C : Type*} [DecidableEq V] {G : SimpleGraph V} {S A B : Finset V}
  {L : V → Finset C} {M : V → V → C → C → Prop}

/-- **Case 7.**  If no 2-cut `{v, w}` with `v ∈ B` separates two vertices of `B`, then no
vertex of `B` has three distinct neighbours in `B`. -/
theorem case7 (hyp : Hyp G S A B L M)
    (hN6 : ∀ v ∈ B, ∀ w ∈ S, w ≠ v → ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ∉ ({v, w} : Finset V) →
      b₂ ∉ ({v, w} : Finset V) → RIn G ↑(S \ {v, w}) b₁ b₂)
    {v x y z : V} (hvB : v ∈ B) (hxB : x ∈ B) (hyB : y ∈ B) (hzB : z ∈ B) (hxy : x ≠ y)
    (hyz : y ≠ z) (hxz : x ≠ z) (hvx : G.Adj v x) (hvy : G.Adj v y) (hvz : G.Adj v z) :
    False := by
  have hRB : ∀ r ∈ ({x, y, z} : Finset V), r ∈ B := by
    intro r hr
    rcases mem_roots_cases hr with rfl | rfl | rfl <;> assumption
  have hRv : ∀ r ∈ ({x, y, z} : Finset V), r ≠ v := by
    intro r hr
    rcases mem_roots_cases hr with rfl | rfl | rfl
    · exact (G.ne_of_adj hvx).symm
    · exact (G.ne_of_adj hvy).symm
    · exact (G.ne_of_adj hvz).symm
  have hmem : ∀ r ∈ ({x, y, z} : Finset V), r ∈ S.erase v := fun r hr =>
    Finset.mem_erase.2 ⟨hRv r hr, hyp.B_sub (hRB r hr)⟩
  have hgood : ∀ u ∈ S.erase v, Good G (S.erase v) x y z u := by
    intro u hu
    have huv : u ≠ v := Finset.ne_of_mem_erase hu
    have huS : u ∈ S := Finset.mem_of_mem_erase hu
    have hpair : ∃ a ∈ ({x, y, z} : Finset V), ∃ b ∈ ({x, y, z} : Finset V),
        a ≠ b ∧ a ≠ u ∧ b ≠ u := by
      by_cases hux : u = x
      · subst hux; exact ⟨y, by simp, z, by simp, hyz, Ne.symm hxy, Ne.symm hxz⟩
      by_cases huy : u = y
      · subst huy; exact ⟨x, by simp, z, by simp, hxz, hxy, Ne.symm hyz⟩
      · exact ⟨x, by simp, y, by simp, hxy, Ne.symm hux, Ne.symm huy⟩
    obtain ⟨a, ha, b, hb, hab, hau, hbu⟩ := hpair
    refine ⟨a, ha, b, hb, hab, hau, hbu, ?_⟩
    refine (hN6 v hvB u huS huv a (hRB a ha) b (hRB b hb) ?_ ?_).mono_set ?_
    · simp [hRv a ha, hau]
    · simp [hRv b hb, hbu]
    · intro t ht
      simp only [Finset.coe_sdiff, Finset.coe_insert, Finset.coe_singleton, Set.mem_sdiff,
        Finset.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
      simp [ht.1, ht.2.1, ht.2.2]
  have hK3 := rootedK3_of_good (hmem x (by simp)) (hmem y (by simp)) (hmem z (by simp)) hxy
    hyz hxz hgood
  exact not_isK5Boundary_of_rootedK3 (B := ↑B) (by simpa using hvB) (by simpa using hxB)
    (by simpa using hyB) (by simpa using hzB) hvx hvy hvz hK3 hyp.bdry

/-- The instance obtained by deleting a boundary vertex `v` (Cases 8 and 9), with the new
boundary `(B \ {v}) ∪ N(v)` given by Lemma 3. -/
theorem hyp_delete (hyp : Hyp G S A B L M) {v : V} (hvB : v ∈ B) (N : Finset V)
    (hN : ∀ a, a ∈ N ↔ a ∈ S ∧ G.Adj v a) (A' : Finset V) (hA' : A' ⊆ A) (hvA' : v ∉ A')
    (L' : V → Finset C) (hL'A : ∀ a ∈ A', L' a = L a)
    (hL'B : ∀ a ∈ B, a ≠ v → a ∉ A' → 3 ≤ (L' a).card)
    (hL'N : ∀ a ∈ S, G.Adj v a → a ∉ B → 3 ≤ (L' a).card)
    (hL'S : ∀ a ∈ S, a ∉ B → ¬ G.Adj v a → L' a = L a) :
    Hyp (restrict G ↑(S.erase v)) (S.erase v) A' (B.erase v ∪ N) L' M := by
  have hA'v : ∀ a ∈ A', a ≠ v := fun a ha h => hvA' (h ▸ ha)
  refine ⟨fun a b h => h.2.1, fun a ha => ?_, fun a ha => ?_, fun a ha b hb hab => ?_, ?_,
    hyp.corr, fun a ha => ?_, fun a ha b hb hab => ?_, fun a ha haA => ?_,
    fun a ha haB => ?_⟩
  · exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hA'v a ha, hyp.A_sub (hA' ha)⟩)
  · rcases Finset.mem_union.1 ha with h | h
    · exact Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase h,
        hyp.B_sub (Finset.mem_of_mem_erase h)⟩
    · obtain ⟨haS, hva⟩ := (hN a).1 h
      exact Finset.mem_erase.2 ⟨(G.ne_of_adj hva).symm, haS⟩
  · refine ⟨hyp.clique a (hA' ha) b (hA' hb) hab, ?_, ?_⟩
    · simp [hA'v a ha, hyp.B_sub (hyp.A_sub (hA' ha))]
    · simp [hA'v b hb, hyp.B_sub (hyp.A_sub (hA' hb))]
  · refine isK5Boundary_delete hyp.bdry (by simpa using hvB) (by simp) (fun u hu => ?_)
    simp only [Finset.coe_union, Finset.coe_erase, Set.mem_union, Set.mem_sdiff,
      Finset.mem_coe, Set.mem_singleton_iff] at hu
    rcases hu with h | h
    · exact Or.inl ⟨h.1, h.2⟩
    · exact Or.inr ((hN u).1 h).2
  · rw [hL'A a ha]; exact hyp.card_A a (hA' ha)
  · rw [hL'A a ha, hL'A b hb]; exact hyp.compat_A a (hA' ha) b (hA' hb) hab
  · rcases Finset.mem_union.1 ha with h | h
    · exact hL'B a (Finset.mem_of_mem_erase h) (Finset.ne_of_mem_erase h) haA
    · obtain ⟨haS, hva⟩ := (hN a).1 h
      by_cases haB : a ∈ B
      · exact hL'B a haB (G.ne_of_adj hva).symm haA
      · exact hL'N a haS hva haB
  · have haS := Finset.mem_of_mem_erase ha
    have hav := Finset.ne_of_mem_erase ha
    have hnB : a ∉ B := fun h => haB (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hav, h⟩))
    have hnN : ¬ G.Adj v a := fun h => haB (Finset.mem_union_right _ ((hN a).2 ⟨haS, h⟩))
    rw [hL'S a haS hnB hnN]
    exact hyp.card_S a haS hnB

/-- Extending a colouring of `G - v` to `v` with a colour of `L v` unused on `N(v)`. -/
theorem col_extend (hGS : ∀ a b, G.Adj a b → a ∈ S) (hM : IsCorrespondence M) {v : V}
    {L' : V → Finset C}
    (hL' : ∀ a ∈ S, a ≠ v → L' a ⊆ L a) (c' : V → C) (hc' : ∀ a ∈ S.erase v, c' a ∈ L' a)
    (hp' : ∀ a b, (restrict G ↑(S.erase v)).Adj a b → ¬ M a b (c' a) (c' b)) (col : C)
    (hcol : col ∈ L v) (hnb : ∀ b, G.Adj v b → ¬ M v b col (c' b)) : Col G S L M := by
  refine ⟨Function.update c' v col, fun a ha => ?_, fun a b hab => ?_⟩
  · by_cases hav : a = v
    · subst hav; simpa using hcol
    · rw [Function.update_of_ne hav]
      exact hL' a ha hav (hc' a (Finset.mem_erase.2 ⟨hav, ha⟩))
  · by_cases hav : a = v
    · subst hav
      have hba : b ≠ a := (G.ne_of_adj hab).symm
      rw [Function.update_self, Function.update_of_ne hba]
      exact hnb b hab
    · by_cases hbv : b = v
      · subst hbv
        rw [Function.update_self, Function.update_of_ne hav]
        exact fun h => hnb a hab.symm (hM.symm _ _ _ _ h)
      · rw [Function.update_of_ne hav, Function.update_of_ne hbv]
        refine hp' a b ⟨hab, ?_, ?_⟩
        · simp [hav, hGS a b hab]
        · simp [hbv, hGS b a hab.symm]

/-- **Case 8** (`G[A]` is a component of `G[B]`): delete a vertex `v ∈ A`, remove the
colour conflicting with its colour from the lists of its neighbours outside `B`, and add
`N(v)` to the boundary. -/
theorem case8 (ih : IHyp V C S.card) (hyp : Hyp G S A B L M) (hAne : A.Nonempty)
    (h8 : ∀ p ∈ A, ∀ q ∈ B, q ∉ A → ¬ G.Adj p q) : Col G S L M := by
  classical
  obtain ⟨v, hvA⟩ := hAne
  have hvB := hyp.A_sub hvA
  have hvS := hyp.B_sub hvB
  obtain ⟨col, hcol⟩ := Finset.card_eq_one.1 (hyp.card_A v hvA)
  let L' : V → Finset C := fun a =>
    if G.Adj v a ∧ a ∉ B then (L a).filter (fun y => ¬ M v a col y) else L a
  have hyp' := hyp_delete hyp hvB (S.filter (G.Adj v)) (by simp) (A.erase v)
    (Finset.erase_subset _ _) (Finset.notMem_erase _ _) L'
    (fun a ha => by simp [L', hyp.A_sub (Finset.mem_of_mem_erase ha)])
    (fun a ha hav haA => by
      have : a ∉ A := fun h => haA (Finset.mem_erase.2 ⟨hav, h⟩)
      simpa [L', ha] using hyp.card_B a ha this)
    (fun a ha hva haB => by
      simp only [L', hva, haB, not_false_eq_true, and_self, ↓reduceIte]
      have h1 := hyp.card_S a ha haB
      have h2 := hyp.corr.card_filter_not_ge v a col (L a)
      omega)
    (fun a ha haB hva => by simp [L', hva])
  have hcard : (S.erase v).card < S.card := Finset.card_erase_lt_of_mem hvS
  obtain ⟨c', hc', hp'⟩ := ih _ _ _ _ _ _ hcard hyp'
  refine col_extend hyp.edge_mem hyp.corr (L' := L') (fun a _ _ => ?_) c' hc' hp' col
    (by simp [hcol]) (fun b hvb => ?_)
  · simp only [L']; split_ifs
    · exact Finset.filter_subset _ _
    · exact subset_rfl
  · have hbS : b ∈ S := hyp.edge_mem b v hvb.symm
    have hbv : b ≠ v := (G.ne_of_adj hvb).symm
    have hcb := hc' b (Finset.mem_erase.2 ⟨hbv, hbS⟩)
    by_cases hbB : b ∈ B
    · by_cases hbA : b ∈ A
      · simp only [L', hvb, hbB, not_true_eq_false, and_false, ↓reduceIte] at hcb
        exact hyp.compat_A v hvA b hbA hbv.symm col (by simp [hcol]) (c' b) hcb
      · exact absurd hvb (h8 v hvA b hbB hbA)
    · simp only [L', hvb, hbB, not_false_eq_true, and_self, ↓reduceIte,
        Finset.mem_filter] at hcb
      exact hcb.2

/-- **Case 9** (some `v ∈ B \ A` is adjacent to `p ∈ A`): reserve two colours `c, d` of
`L v` not conflicting with the colour of `p`, remove the colours conflicting with them from
the lists of the neighbours of `v` outside `B`, delete `v`, and colour `v` with `c` or `d`
avoiding its other neighbour in `B` (there is at most one, by Case 7). -/
theorem case9 (ih : IHyp V C S.card) (hyp : Hyp G S A B L M)
    (h7 : ∀ v ∈ B, ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, x ≠ y → y ≠ z → x ≠ z → G.Adj v x →
      G.Adj v y → G.Adj v z → False)
    {p v : V} (hpA : p ∈ A) (hvB : v ∈ B) (hvA : v ∉ A) (hpv : G.Adj p v) :
    Col G S L M := by
  classical
  have hvS := hyp.B_sub hvB
  have hpB := hyp.A_sub hpA
  have hM := hyp.corr
  obtain ⟨cp, hcp⟩ := Finset.card_eq_one.1 (hyp.card_A p hpA)
  have hcard2 : 1 < ((L v).filter (fun x => ¬ M v p x cp)).card := by
    have h1 := hyp.card_B v hvB hvA
    have h2 := Finset.card_filter_add_card_filter_not (s := L v) (fun x => M v p x cp)
    have h3 : ((L v).filter (fun x => M v p x cp)).card ≤ 1 :=
      Finset.card_le_one.2 fun _ ha _ hb =>
        hM.unique_left (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
    omega
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.1 hcard2
  rw [Finset.mem_filter] at hc hd
  let L' : V → Finset C := fun a =>
    if G.Adj v a ∧ a ∉ B then (L a).filter (fun y => ¬ M v a c y ∧ ¬ M v a d y) else L a
  have hyp' := hyp_delete hyp hvB (S.filter (G.Adj v)) (by simp) A subset_rfl hvA L'
    (fun a ha => by simp [L', hyp.A_sub ha])
    (fun a ha hav haA => by simpa [L', ha] using hyp.card_B a ha haA)
    (fun a ha hva haB => by
      simp only [L', hva, haB, not_false_eq_true, and_self, ↓reduceIte]
      have h1 := hyp.card_S a ha haB
      have hsub : L a ⊆ (L a).filter (fun y => ¬ M v a c y ∧ ¬ M v a d y) ∪
          ((L a).filter (M v a c) ∪ (L a).filter (M v a d)) := by
        intro y hy
        simp only [Finset.mem_union, Finset.mem_filter]
        by_cases h₁ : M v a c y
        · exact Or.inr (Or.inl ⟨hy, h₁⟩)
        · by_cases h₂ : M v a d y
          · exact Or.inr (Or.inr ⟨hy, h₂⟩)
          · exact Or.inl ⟨hy, h₁, h₂⟩
      have h2 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have h3 := Finset.card_union_le ((L a).filter (M v a c)) ((L a).filter (M v a d))
      have h4 := hM.card_filter_le_one v a c (L a)
      have h5 := hM.card_filter_le_one v a d (L a)
      omega)
    (fun a ha haB hva => by simp [L', hva])
  have hcard : (S.erase v).card < S.card := Finset.card_erase_lt_of_mem hvS
  obtain ⟨c', hc', hp'⟩ := ih _ _ _ _ _ _ hcard hyp'
  have hsub : ∀ a ∈ S, a ≠ v → L' a ⊆ L a := by
    intro a _ _
    simp only [L']; split_ifs
    · exact Finset.filter_subset _ _
    · exact subset_rfl
  -- colour `v` from `{c, d}`, avoiding all neighbours in `B` other than `p`
  have finish : ∀ col, (col = c ∨ col = d) →
      (∀ b ∈ B, b ≠ p → G.Adj v b → ¬ M v b col (c' b)) → Col G S L M := by
    intro col hcol hB
    have hcolv : col ∈ L v ∧ ¬ M v p col cp := by rcases hcol with rfl | rfl <;> assumption
    refine col_extend hyp.edge_mem hM hsub c' hc' hp' col hcolv.1 (fun b hvb => ?_)
    have hbS : b ∈ S := hyp.edge_mem b v hvb.symm
    have hbv : b ≠ v := (G.ne_of_adj hvb).symm
    have hcb := hc' b (Finset.mem_erase.2 ⟨hbv, hbS⟩)
    by_cases hbB : b ∈ B
    · by_cases hbp : b = p
      · subst hbp
        simp only [L', hvb, hbB, not_true_eq_false, and_false, ↓reduceIte, hcp,
          Finset.mem_singleton] at hcb
        rw [hcb]; exact hcolv.2
      · exact hB b hbB hbp hvb
    · simp only [L', hvb, hbB, not_false_eq_true, and_self, ↓reduceIte,
        Finset.mem_filter] at hcb
      rcases hcol with rfl | rfl
      · exact hcb.2.1
      · exact hcb.2.2
  by_cases hw : ∃ w ∈ B, w ≠ p ∧ G.Adj v w
  · obtain ⟨w, hwB, hwp, hvw⟩ := hw
    refine finish (if M v w c (c' w) then d else c) (by split_ifs <;> simp)
      (fun b hbB hbp hvb => ?_)
    have hbw : b = w := by
      by_contra hbw
      exact h7 v hvB p hpB w hwB b hbB (Ne.symm hwp) (Ne.symm hbw) (Ne.symm hbp) hpv.symm hvw
        hvb
    subst hbw
    split_ifs with h
    · exact fun h' => hcd (hM.unique_left h h')
    · exact h
  · push Not at hw
    exact finish c (Or.inl rfl) (fun b hbB hbp hvb => absurd hvb (hw b hbB hbp))

end LeanPool.K5MinorFreeChoosability
