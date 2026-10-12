/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Split

/-!
# Cases 3--6 of Wood--Linusson, Lemma 7

Each case lemma takes the induction hypothesis for smaller instances and the hypothesis
that the case applies, and produces the colouring.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V C : Type*} [DecidableEq V] {G : SimpleGraph V} {S A B : Finset V}
  {L : V → Finset C} {M : V → V → C → C → Prop}

/-- **Case 3** (`G` is disconnected). -/
theorem case3 (ih : IHyp V C S.card) (hyp : Hyp G S A B L M) {t₁ t₂ : V} (ht₁ : t₁ ∈ S)
    (ht₂ : t₂ ∈ S) (hsep : ¬ RIn G ↑S t₁ t₂) : Col G S L M := by
  obtain ⟨S₁, S₂, hcov, hint, -, -, hcross, hA, h1, h2, -⟩ :=
    exists_sep (Z := ∅) hyp.edge_mem hyp.clique (hyp.A_sub.trans hyp.B_sub)
      (Finset.empty_subset _) ht₁ (Finset.notMem_empty _) ht₂ (Finset.notMem_empty _)
      (by simpa using hsep)
  refine col_split ih hyp S₁ S₂ hcov hcross h1 h2 hA
    (fun a ha1 ha2 => absurd (hint a ha1 ha2) (Finset.notMem_empty _)) (B ∩ S₂)
    (fun a ha1 ha2 => absurd (hint a ha1 ha2) (Finset.notMem_empty _))
    Finset.inter_subset_right (fun a ha ha2 => Finset.mem_inter.2 ⟨ha, ha2⟩)
    (fun a ha => Or.inl (Finset.mem_inter.1 ha).1)
    (isK5Boundary_anti hyp.bdry (restrict_le _ _) (by simp))

/-- **Case 4** (a cut vertex `v ∈ B`). -/
theorem case4 (ih : IHyp V C S.card) (hyp : Hyp G S A B L M) {v t₁ t₂ : V} (hvB : v ∈ B)
    (ht₁ : t₁ ∈ S) (ht₂ : t₂ ∈ S) (ht₁v : t₁ ≠ v) (ht₂v : t₂ ≠ v)
    (hsep : ¬ RIn G ↑(S \ {v}) t₁ t₂) : Col G S L M := by
  obtain ⟨S₁, S₂, hcov, hint, -, hZ₂, hcross, hA, h1, h2, -⟩ :=
    exists_sep (Z := {v}) hyp.edge_mem hyp.clique (hyp.A_sub.trans hyp.B_sub)
      (Finset.singleton_subset_iff.2 (hyp.B_sub hvB)) ht₁ (by simpa using ht₁v) ht₂
      (by simpa using ht₂v) hsep
  refine col_split ih hyp S₁ S₂ hcov hcross h1 h2 hA (fun a ha1 ha2 b hb1 hb2 hab => ?_)
    (B ∩ S₂) (fun a ha1 ha2 => ?_) Finset.inter_subset_right
    (fun a ha ha2 => Finset.mem_inter.2 ⟨ha, ha2⟩)
    (fun a ha => Or.inl (Finset.mem_inter.1 ha).1)
    (isK5Boundary_anti hyp.bdry (restrict_le _ _) (by simp))
  · have := hint a ha1 ha2
    have := hint b hb1 hb2
    simp_all
  · have := Finset.mem_singleton.1 (hint a ha1 ha2)
    subst this
    exact Finset.mem_inter.2 ⟨hvB, ha2⟩

/-- **Case 5** (a cut vertex `u` separating two vertices of `B`). -/
theorem case5 (ih : IHyp V C S.card) (hyp : Hyp G S A B L M)
    (hconn : ∀ t₁ ∈ S, ∀ t₂ ∈ S, RIn G ↑S t₁ t₂) {u b₁ b₂ : V} (hu : u ∈ S)
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hb₁u : b₁ ≠ u) (hb₂u : b₂ ≠ u)
    (hsep : ¬ RIn G ↑(S \ {u}) b₁ b₂) : Col G S L M := by
  obtain ⟨S₁, S₂, hcov, hint, hZ₁, hZ₂, hcross, hA, h1, h2, hside⟩ :=
    exists_sep (Z := {u}) hyp.edge_mem hyp.clique (hyp.A_sub.trans hyp.B_sub)
      (Finset.singleton_subset_iff.2 hu) (hyp.B_sub hb₁) (by simpa using hb₁u)
      (hyp.B_sub hb₂) (by simpa using hb₂u) hsep
  have hb : ∃ b ∈ B, b ∈ S₁ ∧ b ∉ S₂ := by
    rcases hside with h | h
    · exact ⟨b₁, hb₁, h.1, h.2.1⟩
    · exact ⟨b₂, hb₂, h.1, h.2.1⟩
  obtain ⟨b, hbB, hbS₁, hbS₂⟩ := hb
  have hu₁ : u ∈ S₁ := hZ₁ (Finset.mem_singleton_self u)
  have hu₂ : u ∈ S₂ := hZ₂ (Finset.mem_singleton_self u)
  refine col_split ih hyp S₁ S₂ hcov hcross h1 h2 hA (fun a ha1 ha2 b hb1 hb2 hab => ?_)
    (insert u (B ∩ S₂)) (fun a ha1 ha2 => ?_) ?_ ?_ ?_ ?_
  · have := hint a ha1 ha2
    have := hint b hb1 hb2
    simp_all
  · have := Finset.mem_singleton.1 (hint a ha1 ha2)
    subst this
    exact Finset.mem_insert_self _ _
  · exact Finset.insert_subset hu₂ Finset.inter_subset_right
  · exact fun a ha ha2 => Finset.mem_insert_of_mem (Finset.mem_inter.2 ⟨ha, ha2⟩)
  · intro a ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact Or.inr hu₁
    · exact Or.inl (Finset.mem_inter.1 ha).1
  · refine isK5Boundary_side hyp.bdry hcross (s := ↑S) (z := u) (b := b)
      (fun t _ ht1 ht2 => Finset.mem_singleton.1 (hint t ht1 ht2)) hu₂ hbS₁ hbS₂ hbB
      (hconn b (hyp.B_sub hbB) u hu) (fun x hx => ?_)
    simp only [Finset.coe_insert, Finset.coe_inter, Set.mem_insert_iff, Set.mem_inter_iff,
      Finset.mem_coe] at hx
    rcases hx with rfl | hx
    · exact ⟨hu₂, Or.inr rfl⟩
    · exact ⟨hx.2, Or.inl hx.1⟩

/-- The components needed by Case 6 on one side of the separation. -/
theorem case6_side_data (hyp : Hyp G S A B L M) {S₁ S₂ : Finset V}
    (hcross : ∀ a b, G.Adj a b → (a ∈ S₁ ∧ b ∈ S₁) ∨ (a ∈ S₂ ∧ b ∈ S₂)) {v w : V}
    (hint : ∀ a, a ∈ S₁ → a ∈ S₂ → a ∈ ({v, w} : Finset V)) (hv : v ∈ S₂) (hw : w ∈ S₂)
    (hvB : v ∈ B) (hwS : w ∈ S) (hwv : w ≠ v)
    (hN4 : ∀ x ∈ B, ∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ x → t₂ ≠ x → RIn G ↑(S \ {x}) t₁ t₂)
    (hN5 : ∀ u ∈ S, ∀ b ∈ B, ∀ b' ∈ B, b ≠ u → b' ≠ u → RIn G ↑(S \ {u}) b b')
    {b : V} (hbB : b ∈ B) (hb₁ : b ∈ S₁) (hb₂ : b ∉ S₂) :
    ∃ p p', p ∈ sideComp G S₁ S₂ b ∧ p' ∈ sideComp G S₁ S₂ b ∧ G.Adj p w ∧ G.Adj p' v := by
  have hbv : b ≠ v := fun h => hb₂ (h ▸ hv)
  have hbw : b ≠ w := fun h => hb₂ (h ▸ hw)
  obtain ⟨p, hp₁, hp₂, hbp, hpw⟩ := exists_side_component hcross (s := ↑(S \ {v})) (z := w)
    (fun t ht ht1 ht2 => by
      have h := hint t ht1 ht2
      simp only [Finset.coe_sdiff, Finset.coe_singleton, Set.mem_sdiff, Finset.mem_coe,
        Set.mem_singleton_iff] at ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      tauto) hw hb₁ hb₂ (hN4 v hvB b (hyp.B_sub hbB) w hwS hbv hwv)
  obtain ⟨p', hp'₁, hp'₂, hbp', hp'v⟩ := exists_side_component hcross (s := ↑(S \ {w}))
    (z := v)
    (fun t ht ht1 ht2 => by
      have h := hint t ht1 ht2
      simp only [Finset.coe_sdiff, Finset.coe_singleton, Set.mem_sdiff, Finset.mem_coe,
        Set.mem_singleton_iff] at ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      tauto) hv hb₁ hb₂ (hN5 w hwS b hbB v hvB hbw (Ne.symm hwv))
  exact ⟨p, p', mem_sideComp.2 ⟨hp₁, hp₂, hbp⟩, mem_sideComp.2 ⟨hp'₁, hp'₂, hbp'⟩, hpw, hp'v⟩

/-- The correspondence `M` with the conflicts across the pair `v, w` removed, unless `vw`
is already an edge of `G` (used when the edge `vw` is added in Case 6). -/
def killPair (G : SimpleGraph V) (M : V → V → C → C → Prop) (v w : V) :
    V → V → C → C → Prop :=
  fun a b x y => M a b x y ∧ (G.Adj a b ∨ ¬ ((a = v ∧ b = w) ∨ (a = w ∧ b = v)))

omit [DecidableEq V] in
theorem IsCorrespondence.killPair (hM : IsCorrespondence M) (v w : V) :
    IsCorrespondence (killPair G M v w) := by
  refine ⟨fun a b x y h => ⟨hM.symm _ _ _ _ h.1, ?_⟩,
    fun a b x y y' h h' => hM.unique a b x y y' h.1 h'.1⟩
  rcases h.2 with h2 | h2
  · exact Or.inl h2.symm
  · exact Or.inr (by tauto)

omit [DecidableEq V] in
theorem Col.of_killPair {v w : V} (h : Col (addEdge G v w) S L (killPair G M v w)) :
    Col G S L M := by
  obtain ⟨c, hc, hp⟩ := h
  exact ⟨c, hc, fun a b hab hM => hp a b (le_addEdge G v w hab) ⟨hM, Or.inl hab⟩⟩

/-- **Case 6** (a 2-cut `{v, w}` with `v ∈ B` separating two vertices of `B`).  The edge
`vw` is first added (keeping all hypotheses, by `isK5Boundary_addEdge`), then the instance
is split along the separation. -/
theorem case6 (ih : IHyp V C S.card) (hyp : Hyp G S A B L M)
    (hN4 : ∀ x ∈ B, ∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ x → t₂ ≠ x → RIn G ↑(S \ {x}) t₁ t₂)
    (hN5 : ∀ u ∈ S, ∀ b ∈ B, ∀ b' ∈ B, b ≠ u → b' ≠ u → RIn G ↑(S \ {u}) b b')
    {v w b₁ b₂ : V} (hvB : v ∈ B) (hwS : w ∈ S) (hwv : w ≠ v) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (hb₁Z : b₁ ∉ ({v, w} : Finset V)) (hb₂Z : b₂ ∉ ({v, w} : Finset V))
    (hsep : ¬ RIn G ↑(S \ {v, w}) b₁ b₂) : Col G S L M := by
  have hZS : ({v, w} : Finset V) ⊆ S := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hyp.B_sub hvB
    · exact hwS
  obtain ⟨S₁, S₂, hcov, hint, hZ₁, hZ₂, hcross, hA, h1, h2, hside⟩ :=
    exists_sep (Z := {v, w}) hyp.edge_mem hyp.clique (hyp.A_sub.trans hyp.B_sub) hZS
      (hyp.B_sub hb₁) hb₁Z (hyp.B_sub hb₂) hb₂Z hsep
  have hv₁ : v ∈ S₁ := hZ₁ (by simp)
  have hv₂ : v ∈ S₂ := hZ₂ (by simp)
  have hw₁ : w ∈ S₁ := hZ₁ (by simp)
  have hw₂ : w ∈ S₂ := hZ₂ (by simp)
  have hsides : ∃ ba bb, ba ∈ B ∧ ba ∈ S₁ ∧ ba ∉ S₂ ∧ bb ∈ B ∧ bb ∈ S₂ ∧ bb ∉ S₁ := by
    rcases hside with h | h
    · exact ⟨b₁, b₂, hb₁, h.1, h.2.1, hb₂, h.2.2.1, h.2.2.2⟩
    · exact ⟨b₂, b₁, hb₂, h.1, h.2.1, hb₁, h.2.2.1, h.2.2.2⟩
  obtain ⟨ba, bb, hbaB, hba₁, hba₂, hbbB, hbb₂, hbb₁⟩ := hsides
  obtain ⟨pa, pa', hpa, hpa', hpaw, hpa'v⟩ :=
    case6_side_data hyp hcross hint hv₂ hw₂ hvB hwS hwv hN4 hN5 hbaB hba₁ hba₂
  obtain ⟨pb, pb', hpb, hpb', hpbw, hpb'v⟩ :=
    case6_side_data hyp (fun a b hab => (hcross a b hab).symm)
      (fun a ha2 ha1 => hint a ha1 ha2) hv₁ hw₁ hvB hwS hwv hN4 hN5 hbbB hbb₂ hbb₁
  have hZ' : ∀ t, t ∈ S₁ → t ∈ S₂ → t = v ∨ t = w := fun t h1 h2 => by
    simpa using hint t h1 h2
  -- add the edge `vw`
  have hbd' : IsK5Boundary (addEdge G v w) ↑B :=
    isK5Boundary_addEdge hyp.bdry hcross
      (fun b hb => Finset.mem_union.1 (hcov ▸ hyp.B_sub hb)) hZ' hv₁ hv₂ hw₁ hw₂ hvB
      hbaB hba₁ hba₂ hpa hpa' hpaw hpa'v hbbB hbb₂ hbb₁ hpb hpb' hpbw hpb'v
  have hyp' : Hyp (addEdge G v w) S A B L (killPair G M v w) := by
    refine ⟨fun a b hab => ?_, hyp.A_sub, hyp.B_sub,
      fun a ha b hb hab => le_addEdge G v w (hyp.clique a ha b hb hab), hbd',
      hyp.corr.killPair v w, hyp.card_A,
      fun a ha b hb hab x hx y hy h => hyp.compat_A a ha b hb hab x hx y hy h.1, hyp.card_B,
      hyp.card_S⟩
    rcases hab with h | ⟨-, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩
    · exact hyp.edge_mem a b h
    · exact hyp.B_sub hvB
    · exact hwS
  have hcross' : ∀ a b, (addEdge G v w).Adj a b →
      (a ∈ S₁ ∧ b ∈ S₁) ∨ (a ∈ S₂ ∧ b ∈ S₂) := by
    intro a b hab
    rcases hab with h | ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact hcross a b h
    · exact Or.inl ⟨hv₁, hw₁⟩
    · exact Or.inl ⟨hw₁, hv₁⟩
  refine Col.of_killPair (v := v) (w := w) ?_
  refine col_split ih hyp' S₁ S₂ hcov hcross' h1 h2 hA (fun a ha1 ha2 b hb1 hb2 hab => ?_)
    (insert w (B ∩ S₂)) (fun a ha1 ha2 => ?_) ?_ ?_ ?_ ?_
  · rcases hZ' a ha1 ha2 with rfl | rfl <;> rcases hZ' b hb1 hb2 with rfl | rfl
    · exact absurd rfl hab
    · exact addEdge_adj_self G hab
    · exact (addEdge_adj_self G hab.symm).symm
    · exact absurd rfl hab
  · rcases hZ' a ha1 ha2 with rfl | rfl
    · exact Finset.mem_insert_of_mem (Finset.mem_inter.2 ⟨hvB, hv₂⟩)
    · exact Finset.mem_insert_self _ _
  · exact Finset.insert_subset hw₂ Finset.inter_subset_right
  · exact fun a ha ha2 => Finset.mem_insert_of_mem (Finset.mem_inter.2 ⟨ha, ha2⟩)
  · intro a ha
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact Or.inr hw₁
    · exact Or.inl (Finset.mem_inter.1 ha).1
  · have hbav : ba ≠ v := fun h => hba₂ (h ▸ hv₂)
    refine isK5Boundary_side hbd' hcross' (s := ↑(S \ {v})) (z := w) (b := ba)
      (fun t ht ht1 ht2 => ?_) hw₂ hba₁ hba₂ hbaB
      ((hN4 v hvB ba (hyp.B_sub hbaB) w hwS hbav hwv).mono_graph (le_addEdge G v w))
      (fun x hx => ?_)
    · simp only [Finset.coe_sdiff, Finset.coe_singleton, Set.mem_sdiff, Finset.mem_coe,
        Set.mem_singleton_iff] at ht
      rcases hZ' t ht1 ht2 with h | h
      · exact absurd h ht.2
      · exact h
    · simp only [Finset.coe_insert, Finset.coe_inter, Set.mem_insert_iff, Set.mem_inter_iff,
        Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact ⟨hw₂, Or.inr rfl⟩
      · exact ⟨hx.2, Or.inl hx.1⟩

end LeanPool.K5MinorFreeChoosability
