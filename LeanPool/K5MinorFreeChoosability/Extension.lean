/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Cases789

/-!
# Wood--Linusson, Lemma 7, and Škrekovski's theorem

* `exists_listColouring_of_boundary`: **Lemma 7** of Wood--Linusson (2010) for every finite
  simple graph, every clique `A ⊆ B` and every `K_5`-minor-free boundary `B`, with arbitrary
  finite lists over an arbitrary colour type.
* `exists_listColouring_of_k5MinorFree` / `choosableWith_five_of_k5MinorFree`:
  **Škrekovski (1998)**: every finite `K_5`-minor-free graph is 5-choosable, for lists over
  any colour type.  The proof is the one of Wood--Linusson (Lemma 7 with `A = B = ∅`).
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

section Internal

variable {V C : Type*} [DecidableEq V] {G : SimpleGraph V} {S A B : Finset V}
  {L : V → Finset C} {M : V → V → C → C → Prop}

omit [DecidableEq V] in
theorem Col.mono_list {L₁ : V → Finset C} (h : Col G S L₁ M) (hL : ∀ a ∈ S, L₁ a ⊆ L a) :
    Col G S L M := by
  obtain ⟨c, hc, hp⟩ := h
  exact ⟨c, fun a ha => hL a ha (hc a ha), hp⟩

/-- Lemma 7 for instances with `A ≠ ∅`, assuming it for smaller instances: Cases 3--9. -/
theorem col_of_nonempty (ih : IHyp V C S.card) (hyp : Hyp G S A B L M) (hA : A.Nonempty) :
    Col G S L M := by
  classical
  by_cases h3 : ∃ t₁ ∈ S, ∃ t₂ ∈ S, ¬ RIn G ↑S t₁ t₂
  · obtain ⟨t₁, ht₁, t₂, ht₂, h⟩ := h3
    exact case3 ih hyp ht₁ ht₂ h
  push Not at h3
  by_cases h4 : ∃ v ∈ B, ∃ t₁ ∈ S, ∃ t₂ ∈ S, t₁ ≠ v ∧ t₂ ≠ v ∧ ¬ RIn G ↑(S \ {v}) t₁ t₂
  · obtain ⟨v, hv, t₁, ht₁, t₂, ht₂, ht₁v, ht₂v, h⟩ := h4
    exact case4 ih hyp hv ht₁ ht₂ ht₁v ht₂v h
  push Not at h4
  by_cases h5 : ∃ u ∈ S, ∃ b₁ ∈ B, ∃ b₂ ∈ B, b₁ ≠ u ∧ b₂ ≠ u ∧ ¬ RIn G ↑(S \ {u}) b₁ b₂
  · obtain ⟨u, hu, b₁, hb₁, b₂, hb₂, hb₁u, hb₂u, h⟩ := h5
    exact case5 ih hyp h3 hu hb₁ hb₂ hb₁u hb₂u h
  push Not at h5
  by_cases h6 : ∃ v ∈ B, ∃ w ∈ S, w ≠ v ∧ ∃ b₁ ∈ B, ∃ b₂ ∈ B, b₁ ∉ ({v, w} : Finset V) ∧
      b₂ ∉ ({v, w} : Finset V) ∧ ¬ RIn G ↑(S \ {v, w}) b₁ b₂
  · obtain ⟨v, hv, w, hw, hwv, b₁, hb₁, b₂, hb₂, hb₁Z, hb₂Z, h⟩ := h6
    exact case6 ih hyp h4 h5 hv hw hwv hb₁ hb₂ hb₁Z hb₂Z h
  have h6' : ∀ v ∈ B, ∀ w ∈ S, w ≠ v → ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ∉ ({v, w} : Finset V) →
      b₂ ∉ ({v, w} : Finset V) → RIn G ↑(S \ {v, w}) b₁ b₂ := by
    intro v hv w hw hwv b₁ hb₁ b₂ hb₂ hb₁Z hb₂Z
    by_contra h
    exact h6 ⟨v, hv, w, hw, hwv, b₁, hb₁, b₂, hb₂, hb₁Z, hb₂Z, h⟩
  have h7 : ∀ v ∈ B, ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, x ≠ y → y ≠ z → x ≠ z → G.Adj v x →
      G.Adj v y → G.Adj v z → False :=
    fun v hv x hx y hy z hz hxy hyz hxz hvx hvy hvz =>
      case7 hyp h6' hv hx hy hz hxy hyz hxz hvx hvy hvz
  by_cases h8 : ∀ p ∈ A, ∀ q ∈ B, q ∉ A → ¬ G.Adj p q
  · exact case8 ih hyp hA h8
  · push Not at h8
    obtain ⟨p, hp, q, hq, hqA, hpq⟩ := h8
    exact case9 ih hyp h7 hp hq hqA hpq

/-- Lemma 7 for an instance, assuming it for smaller instances: Cases 1 and 2 reduce to
`A ≠ ∅`. -/
theorem col_of_hyp [Nonempty C] (ih : IHyp V C S.card) (hyp : Hyp G S A B L M) :
    Col G S L M := by
  classical
  by_cases hA : A.Nonempty
  · exact col_of_nonempty ih hyp hA
  rw [Finset.not_nonempty_iff_eq_empty] at hA
  subst hA
  -- precolour a single vertex `v` with a colour `col` of its list
  have precolour : ∀ v ∈ S, ∀ col ∈ L v, ∀ B' : Finset V, v ∈ B' → B' ⊆ S →
      IsK5Boundary G ↑B' → (∀ a ∈ B', a ≠ v → 3 ≤ (L a).card) →
      (∀ a ∈ S, a ∉ B' → 5 ≤ (L a).card) → Col G S L M := by
    intro v hvS col hcol B' hvB' hB'S hbd hcB hcS
    have hyp' : Hyp G S {v} B' (Function.update L v {col}) M := by
      refine ⟨hyp.edge_mem, Finset.singleton_subset_iff.2 hvB', hB'S, fun a ha b hb hab => ?_,
        hbd, hyp.corr, fun a ha => ?_, fun a ha b hb hab => ?_, fun a ha haA => ?_,
        fun a ha haB => ?_⟩
      · rw [Finset.mem_singleton] at ha hb; exact absurd (ha.trans hb.symm) hab
      · rw [Finset.mem_singleton] at ha; subst ha; simp
      · rw [Finset.mem_singleton] at ha hb; exact absurd (ha.trans hb.symm) hab
      · have hav : a ≠ v := by simpa using haA
        rw [Function.update_of_ne hav]; exact hcB a ha hav
      · have hav : a ≠ v := fun h => haB (h ▸ hvB')
        rw [Function.update_of_ne hav]; exact hcS a ha haB
    refine (col_of_nonempty ih hyp' ⟨v, Finset.mem_singleton_self v⟩).mono_list
      (fun a _ => ?_)
    by_cases hav : a = v
    · subst hav; simpa using hcol
    · rw [Function.update_of_ne hav]
  by_cases hB : B.Nonempty
  · -- Case 2
    obtain ⟨v, hvB⟩ := hB
    have h3 := hyp.card_B v hvB (Finset.notMem_empty v)
    obtain ⟨col, hcol⟩ := Finset.card_pos.1 (by omega : 0 < (L v).card)
    exact precolour v (hyp.B_sub hvB) col hcol B hvB hyp.B_sub hyp.bdry
      (fun a ha _ => hyp.card_B a ha (Finset.notMem_empty a)) hyp.card_S
  rw [Finset.not_nonempty_iff_eq_empty] at hB
  subst hB
  by_cases hS : S.Nonempty
  · -- Case 1
    obtain ⟨v, hvS⟩ := hS
    have h5 := hyp.card_S v hvS (Finset.notMem_empty v)
    obtain ⟨col, hcol⟩ := Finset.card_pos.1 (by omega : 0 < (L v).card)
    refine precolour v hvS col hcol {v} (Finset.mem_singleton_self v)
      (Finset.singleton_subset_iff.2 hvS) ?_ (fun a ha hav => absurd (Finset.mem_singleton.1 ha)
        hav) (fun a ha _ => hyp.card_S a ha (Finset.notMem_empty a))
    have := isK5Boundary_singleton (by simpa using hyp.bdry) v
    simpa using this
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    subst hS
    exact ⟨fun _ => Classical.arbitrary C, fun a ha => absurd ha (Finset.notMem_empty a),
      fun a b hab => absurd (hyp.edge_mem a b hab) (Finset.notMem_empty a)⟩

/-- Lemma 7 for all instances, by strong induction on the number of vertices. -/
theorem iHyp_all [Nonempty C] : ∀ n, IHyp V C n := by
  intro n
  induction n with
  | zero => intro G S A B L M h; omega
  | succ n ih =>
    intro G S A B L M hlt hyp
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h | h
    · exact ih G S A B L M h hyp
    · subst h
      exact col_of_hyp ih hyp

end Internal

variable {V C : Type*}

/-- **Wood--Linusson (2010), Lemma 7, for correspondence (DP) colouring.**
Let `G` be a finite simple graph, `A ⊆ B` sets of vertices such that `A` is a clique and
`B` is a `K_5`-minor-free boundary of `G`.  Let `M` be a correspondence (a symmetric family
of partial matchings between colours) and `L` finite lists over an arbitrary colour type
such that the vertices of `A` have singleton lists whose colours pairwise do not conflict
under `M`, the vertices of `B \ A` have at least three colours, and all other vertices
have at least five colours.  Then `G` has an `(L, M)`-colouring.

The proof is Wood--Linusson's argument; in Case 6 the inserted edge `vw` carries the empty
matching (see `killPair`), so that the relabelling and gluing steps transport verbatim. -/
theorem exists_dpColouring_of_boundary [Finite V] (G : SimpleGraph V) (A B : Finset V)
    (hAB : A ⊆ B) (hA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → G.Adj a b) (hB : IsK5Boundary G ↑B)
    (L : V → Finset C) (M : V → V → C → C → Prop) (hM : IsCorrespondence M)
    (hLA : ∀ a ∈ A, (L a).card = 1)
    (hLcompat : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ x ∈ L a, ∀ y ∈ L b, ¬ M a b x y)
    (hLB : ∀ a ∈ B, a ∉ A → 3 ≤ (L a).card) (hLV : ∀ a, a ∉ B → 5 ≤ (L a).card) :
    DPColourable G L M := by
  classical
  have := Fintype.ofFinite V
  rcases isEmpty_or_nonempty V with hV | ⟨⟨v₀⟩⟩
  · exact ⟨fun v => isEmptyElim v, fun v => isEmptyElim v, fun v => isEmptyElim v⟩
  have hne : (L v₀).Nonempty := by
    by_cases h1 : v₀ ∈ A
    · exact Finset.card_pos.1 (by rw [hLA v₀ h1]; norm_num)
    by_cases h2 : v₀ ∈ B
    · exact Finset.card_pos.1 (by have := hLB v₀ h2 h1; omega)
    · exact Finset.card_pos.1 (by have := hLV v₀ h2; omega)
  have : Nonempty C := ⟨hne.choose⟩
  have hyp : Hyp G Finset.univ A B L M :=
    ⟨fun _ _ _ => Finset.mem_univ _, hAB, Finset.subset_univ _, hA, hB, hM, hLA, hLcompat,
      hLB, fun a _ haB => hLV a haB⟩
  obtain ⟨c, hc, hp⟩ := iHyp_all _ G Finset.univ A B L M (Nat.lt_succ_self _) hyp
  exact ⟨c, fun v => hc v (Finset.mem_univ v), hp⟩

/-- **Wood--Linusson (2010), Lemma 7: the general boundary extension.**
Let `G` be a finite simple graph, `A ⊆ B` sets of vertices such that `A` is a clique and
`B` is a `K_5`-minor-free boundary of `G` (the apex extension `G^{B+α}`, obtained by adding
one fresh vertex adjacent exactly to `B`, has no `K_5` minor; this already implies that `G`
has no `K_5` minor, see `k5MinorFree_of_isK5Boundary`).  Let `L` assign finite lists over
an arbitrary colour type `C` such that the vertices of `A` have singleton lists with
pairwise different colours, the vertices of `B \ A` have at least three colours, and all
other vertices have at least five colours.  Then `G` has a proper colouring from `L`. -/
theorem exists_listColouring_of_boundary [Finite V] (G : SimpleGraph V) (A B : Finset V)
    (hAB : A ⊆ B) (hA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → G.Adj a b) (hB : IsK5Boundary G ↑B)
    (L : V → Finset C) (hLA : ∀ a ∈ A, (L a).card = 1)
    (hLinj : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → L a ≠ L b) (hLB : ∀ a ∈ B, a ∉ A → 3 ≤ (L a).card)
    (hLV : ∀ a, a ∉ B → 5 ≤ (L a).card) : ListColourable G L := by
  refine dpColourable_eq_iff_listColourable.1 (exists_dpColouring_of_boundary G A B hAB hA hB
    L _ IsCorrespondence.eq hLA (fun a ha b hb hab x hx y hy hxy => ?_) hLB hLV)
  obtain ⟨x', hx'⟩ := Finset.card_eq_one.1 (hLA a ha)
  obtain ⟨y', hy'⟩ := Finset.card_eq_one.1 (hLA b hb)
  rw [hx', Finset.mem_singleton] at hx
  rw [hy', Finset.mem_singleton] at hy
  exact hLinj a ha b hb hab (by rw [hx', hy', ← hx, ← hy, hxy])

/-- **DP-5-colourability of `K_5`-minor-free graphs** (Li--Wang (2022), Theorem 1.1),
proved here by Wood--Linusson's argument rather than via Wagner's structure theorem:
every finite `K_5`-minor-free graph has an `(L, M)`-colouring for every correspondence `M`
and all finite lists of size at least five over an arbitrary colour type. -/
theorem exists_dpColouring_of_k5MinorFree [Finite V] (G : SimpleGraph V)
    (hG : CliqueMinorFree G 5) (L : V → Finset C) (M : V → V → C → C → Prop)
    (hM : IsCorrespondence M) (hL : ∀ v, 5 ≤ (L v).card) : DPColourable G L M :=
  exists_dpColouring_of_boundary G ∅ ∅ subset_rfl (by simp)
    (by simpa using isK5Boundary_empty_iff.2 hG) L M hM (by simp) (by simp) (by simp)
    (fun a _ => hL a)

/-- DP-5-colourability of finite `K_5`-minor-free graphs, for every colour type. -/
theorem dpColourableWith_five_of_k5MinorFree [Finite V] (G : SimpleGraph V)
    (hG : CliqueMinorFree G 5) (C : Type*) : DPColourableWith G C 5 :=
  fun L M hM hL => exists_dpColouring_of_k5MinorFree G hG L M hM hL

/-- **Škrekovski (1998): every finite `K_5`-minor-free graph is 5-choosable**, for finite
lists over an arbitrary colour type.  (Proof: Wood--Linusson, Lemma 7 with `A = B = ∅`.) -/
theorem exists_listColouring_of_k5MinorFree [Finite V] (G : SimpleGraph V)
    (hG : CliqueMinorFree G 5) (L : V → Finset C) (hL : ∀ v, 5 ≤ (L v).card) :
    ListColourable G L :=
  exists_listColouring_of_boundary G ∅ ∅ subset_rfl (by simp)
    (by simpa using isK5Boundary_empty_iff.2 hG) L (by simp) (by simp) (by simp)
    (fun a _ => hL a)

/-- **Škrekovski (1998)** in choosability form: a finite `K_5`-minor-free graph is
5-choosable with respect to every colour type. -/
theorem choosableWith_five_of_k5MinorFree [Finite V] (G : SimpleGraph V)
    (hG : CliqueMinorFree G 5) (C : Type*) : ChoosableWith G C 5 :=
  fun L hL => exists_listColouring_of_k5MinorFree G hG L hL

end LeanPool.K5MinorFreeChoosability
