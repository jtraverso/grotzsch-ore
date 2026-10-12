/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Correspondence
public import LeanPool.K5MinorFreeChoosability.Boundary

/-!
# Instances of Wood--Linusson, Lemma 7, and splitting along separations

An *instance* `Hyp G S A B L M` of Lemma 7 consists of a graph `G` whose edges lie inside
the finite vertex set `S`, a clique `A ⊆ B ⊆ S`, a `K_5`-minor-free boundary `B`, a
list assignment `L` with the cardinality conditions of Lemma 7 and a correspondence `M`
(for ordinary list colouring, `M u v x y ↔ x = y`).  `Col G S L M` asserts an
`(L, M)`-colouring of `G` on `S`.  Working with correspondences costs nothing in the
argument and yields the DP-colouring version of Lemma 7 at the same time.

`col_split` performs the common step of Cases 3--6: colour the side containing `A` first,
then precolour the separator in the other side and colour it.  `exists_sep` produces the
separations from a failure of connectivity.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V C : Type*} [DecidableEq V]

/-- The hypotheses of Wood--Linusson, Lemma 7, for the graph `G` on the vertex set `S`. -/
structure Hyp (G : SimpleGraph V) (S A B : Finset V) (L : V → Finset C)
    (M : V → V → C → C → Prop) : Prop where
  edge_mem : ∀ a b, G.Adj a b → a ∈ S
  A_sub : A ⊆ B
  B_sub : B ⊆ S
  clique : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → G.Adj a b
  bdry : IsK5Boundary G ↑B
  corr : IsCorrespondence M
  card_A : ∀ a ∈ A, (L a).card = 1
  compat_A : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ x ∈ L a, ∀ y ∈ L b, ¬ M a b x y
  card_B : ∀ a ∈ B, a ∉ A → 3 ≤ (L a).card
  card_S : ∀ a ∈ S, a ∉ B → 5 ≤ (L a).card

/-- An `(L, M)`-colouring of `G` choosing from the lists `L` on `S`. -/
def Col (G : SimpleGraph V) (S : Finset V) (L : V → Finset C) (M : V → V → C → C → Prop) :
    Prop :=
  ∃ c : V → C, (∀ a ∈ S, c a ∈ L a) ∧ ∀ a b, G.Adj a b → ¬ M a b (c a) (c b)

/-- Induction hypothesis: Lemma 7 holds for all instances with fewer than `n` vertices. -/
def IHyp (V C : Type*) [DecidableEq V] (n : ℕ) : Prop :=
  ∀ (G : SimpleGraph V) (S A B : Finset V) (L : V → Finset C) (M : V → V → C → C → Prop),
    S.card < n → Hyp G S A B L M → Col G S L M

omit [DecidableEq V] in
theorem Col.mono_graph {G G' : SimpleGraph V} {S : Finset V} {L : V → Finset C}
    {M : V → V → C → C → Prop} (h : Col G' S L M) (hG : G ≤ G') : Col G S L M := by
  obtain ⟨c, hc, hp⟩ := h
  exact ⟨c, hc, fun a b hab => hp a b (hG hab)⟩

/-- Gluing two colourings that agree on the intersection. -/
theorem col_glue {G : SimpleGraph V} {S S₁ S₂ : Finset V} {L : V → Finset C}
    {M : V → V → C → C → Prop} (hcover : S ⊆ S₁ ∪ S₂)
    (hcross : ∀ a b, G.Adj a b → (a ∈ S₁ ∧ b ∈ S₁) ∨ (a ∈ S₂ ∧ b ∈ S₂))
    (c₁ c₂ : V → C) (h₁ : ∀ a ∈ S₁, c₁ a ∈ L a) (h₂ : ∀ a ∈ S₂, a ∉ S₁ → c₂ a ∈ L a)
    (hp₁ : ∀ a b, G.Adj a b → a ∈ S₁ → b ∈ S₁ → ¬ M a b (c₁ a) (c₁ b))
    (hp₂ : ∀ a b, G.Adj a b → a ∈ S₂ → b ∈ S₂ → ¬ M a b (c₂ a) (c₂ b))
    (hagree : ∀ a ∈ S₁, a ∈ S₂ → c₁ a = c₂ a) : Col G S L M := by
  classical
  refine ⟨fun a => if a ∈ S₁ then c₁ a else c₂ a, fun a ha => ?_, fun a b hab => ?_⟩
  · by_cases h : a ∈ S₁
    · simp [h, h₁ a h]
    · have : a ∈ S₂ := by
        rcases Finset.mem_union.1 (hcover ha) with h' | h'
        · exact absurd h' h
        · exact h'
      simp [h, h₂ a this h]
  · rcases hcross a b hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · simp only [ha, hb, ↓reduceIte]
      exact hp₁ a b hab ha hb
    · have ea : (if a ∈ S₁ then c₁ a else c₂ a) = c₂ a := by
        split_ifs with h
        · exact hagree a h ha
        · rfl
      have eb : (if b ∈ S₁ then c₁ b else c₂ b) = c₂ b := by
        split_ifs with h
        · exact hagree b h hb
        · rfl
      simp only [ea, eb]
      exact hp₂ a b hab ha hb

/-- **The splitting step of Cases 3--6.**  Given a separation `(S₁, S₂)` of an instance,
with `A ⊆ S₁`, a clique separator `S₁ ∩ S₂`, and a boundary `B₂` of `G[S₂]` containing the
separator and `B ∩ S₂`, colour `G[S₁]` by induction, precolour the separator in `G[S₂]`
and colour `G[S₂]` by induction. -/
theorem col_split {G : SimpleGraph V} {S A B : Finset V} {L : V → Finset C}
    {M : V → V → C → C → Prop} (ih : IHyp V C S.card) (hyp : Hyp G S A B L M)
    (S₁ S₂ : Finset V)
    (hcover : S₁ ∪ S₂ = S)
    (hcross : ∀ a b, G.Adj a b → (a ∈ S₁ ∧ b ∈ S₁) ∨ (a ∈ S₂ ∧ b ∈ S₂))
    (h₁ : S₁.card < S.card) (h₂ : S₂.card < S.card) (hA : A ⊆ S₁)
    (hZ : ∀ a ∈ S₁, a ∈ S₂ → ∀ b ∈ S₁, b ∈ S₂ → a ≠ b → G.Adj a b)
    (B₂ : Finset V) (hZB₂ : ∀ a ∈ S₁, a ∈ S₂ → a ∈ B₂) (hB₂S : B₂ ⊆ S₂)
    (hBB₂ : ∀ a ∈ B, a ∈ S₂ → a ∈ B₂) (hB₂B : ∀ a ∈ B₂, a ∈ B ∨ a ∈ S₁)
    (hbd : IsK5Boundary (restrict G ↑S₂) ↑B₂) : Col G S L M := by
  classical
  -- the side containing `A`
  have hyp₁ : Hyp (restrict G ↑S₁) S₁ A (B ∩ S₁) L M := by
    refine ⟨fun a b h => h.2.1, fun a ha => Finset.mem_inter.2 ⟨hyp.A_sub ha, hA ha⟩,
      Finset.inter_subset_right, fun a ha b hb hab => ⟨hyp.clique a ha b hb hab, hA ha, hA hb⟩,
      isK5Boundary_anti hyp.bdry (restrict_le _ _) (by simp), hyp.corr, hyp.card_A,
      hyp.compat_A,
      fun a ha haA => hyp.card_B a (Finset.mem_inter.1 ha).1 haA, fun a ha haB => ?_⟩
    refine hyp.card_S a (hcover ▸ Finset.mem_union_left _ ha) (fun h => haB ?_)
    exact Finset.mem_inter.2 ⟨h, ha⟩
  obtain ⟨c₁, hc₁, hp₁⟩ := ih _ _ _ _ _ _ h₁ hyp₁
  -- the other side, with the separator precoloured
  let L₂ : V → Finset C := fun a => if a ∈ S₁ then {c₁ a} else L a
  have hyp₂ : Hyp (restrict G ↑S₂) S₂ (S₁ ∩ S₂) B₂ L₂ M := by
    refine ⟨fun a b h => h.2.1, fun a ha => ?_, hB₂S, fun a ha b hb hab => ?_, hbd, hyp.corr,
      fun a ha => ?_, fun a ha b hb hab => ?_, fun a ha haZ => ?_, fun a ha haB => ?_⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_inter.1 ha; exact hZB₂ a h1 h2
    · obtain ⟨ha1, ha2⟩ := Finset.mem_inter.1 ha
      obtain ⟨hb1, hb2⟩ := Finset.mem_inter.1 hb
      exact ⟨hZ a ha1 ha2 b hb1 hb2 hab, ha2, hb2⟩
    · simp [L₂, (Finset.mem_inter.1 ha).1]
    · obtain ⟨ha1, ha2⟩ := Finset.mem_inter.1 ha
      obtain ⟨hb1, hb2⟩ := Finset.mem_inter.1 hb
      simp only [L₂, ha1, hb1, ↓reduceIte, Finset.mem_singleton]
      rintro x rfl y rfl
      exact hp₁ a b ⟨hZ a ha1 ha2 b hb1 hb2 hab, ha1, hb1⟩
    · have ha2 := hB₂S ha
      have ha1 : a ∉ S₁ := fun h => haZ (Finset.mem_inter.2 ⟨h, ha2⟩)
      have haB : a ∈ B := by
        rcases hB₂B a ha with h | h
        · exact h
        · exact absurd h ha1
      simp only [L₂, ha1, ↓reduceIte]
      exact hyp.card_B a haB (fun h => ha1 (hA h))
    · have ha1 : a ∉ S₁ := fun h => haB (hZB₂ a h ha)
      simp only [L₂, ha1, ↓reduceIte]
      exact hyp.card_S a (hcover ▸ Finset.mem_union_right _ ha) (fun h => haB (hBB₂ a h ha))
  obtain ⟨c₂, hc₂, hp₂⟩ := ih _ _ _ _ _ _ h₂ hyp₂
  refine col_glue (S₁ := S₁) (S₂ := S₂) (hcover ▸ subset_rfl) hcross c₁ c₂ hc₁
    (fun a ha ha1 => by simpa [L₂, ha1] using hc₂ a ha)
    (fun a b hab ha hb => hp₁ a b ⟨hab, ha, hb⟩) (fun a b hab ha hb => hp₂ a b ⟨hab, ha, hb⟩)
    (fun a ha1 ha2 => ?_)
  have := hc₂ a ha2
  simp only [L₂, ha1, ↓reduceIte, Finset.mem_singleton] at this
  exact this.symm

/-- **Separations from disconnection.**  If two vertices `t₁, t₂ ∈ S \ Z` are not connected
in `G[S \ Z]`, then `S` splits as `S₁ ∪ S₂` with `S₁ ∩ S₂ = Z`, no edges between
`S₁ \ S₂` and `S₂ \ S₁`, the clique `A` inside `S₁`, both sides proper, and `t₁, t₂` on
different sides. -/
theorem exists_sep {G : SimpleGraph V} {S A Z : Finset V} (hGS : ∀ a b, G.Adj a b → a ∈ S)
    (hAcl : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → G.Adj a b) (hAS : A ⊆ S) (hZS : Z ⊆ S)
    {t₁ t₂ : V} (ht₁ : t₁ ∈ S) (ht₁Z : t₁ ∉ Z) (ht₂ : t₂ ∈ S) (ht₂Z : t₂ ∉ Z)
    (hsep : ¬ RIn G ↑(S \ Z) t₁ t₂) :
    ∃ S₁ S₂ : Finset V, S₁ ∪ S₂ = S ∧ (∀ a, a ∈ S₁ → a ∈ S₂ → a ∈ Z) ∧ Z ⊆ S₁ ∧ Z ⊆ S₂ ∧
      (∀ a b, G.Adj a b → (a ∈ S₁ ∧ b ∈ S₁) ∨ (a ∈ S₂ ∧ b ∈ S₂)) ∧ A ⊆ S₁ ∧
      S₁.card < S.card ∧ S₂.card < S.card ∧
      ((t₁ ∈ S₁ ∧ t₁ ∉ S₂ ∧ t₂ ∈ S₂ ∧ t₂ ∉ S₁) ∨ (t₂ ∈ S₁ ∧ t₂ ∉ S₂ ∧ t₁ ∈ S₂ ∧ t₁ ∉ S₁)) := by
  classical
  set K := (S \ Z).filter (fun t => RIn G ↑(S \ Z) t₁ t) with hK
  have hmemK : ∀ t, t ∈ K ↔ t ∈ S ∧ t ∉ Z ∧ RIn G ↑(S \ Z) t₁ t := by
    intro t; simp [K, and_assoc]
  have hclos : ∀ a b, a ∈ K → b ∈ S → b ∉ Z → G.Adj a b → b ∈ K := by
    intro a b ha hb hbZ hab
    obtain ⟨haS, haZ, hra⟩ := (hmemK a).1 ha
    exact (hmemK b).2 ⟨hb, hbZ, hra.tail hab (by simp [haS, haZ]) (by simp [hb, hbZ])⟩
  have ht₁K : t₁ ∈ K := (hmemK t₁).2 ⟨ht₁, ht₁Z, RIn.refl _⟩
  have ht₂K : t₂ ∉ K := fun h => hsep ((hmemK t₂).1 h).2.2
  have hKZ : ∀ t ∈ K, t ∉ Z := fun t ht => ((hmemK t).1 ht).2.1
  have hKS : K ⊆ S := fun t ht => ((hmemK t).1 ht).1
  set P := K ∪ Z
  set Q := S \ K
  have hPQ : P ∪ Q = S := by
    ext t; simp only [P, Q, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ((h | h) | h)
      · exact hKS h
      · exact hZS h
      · exact h.1
    · intro h; by_cases hk : t ∈ K
      · exact Or.inl (Or.inl hk)
      · exact Or.inr ⟨h, hk⟩
  have hPQZ : ∀ a, a ∈ P → a ∈ Q → a ∈ Z := by
    intro a haP haQ
    simp only [P, Q, Finset.mem_union, Finset.mem_sdiff] at haP haQ
    rcases haP with h | h
    · exact absurd h haQ.2
    · exact h
  have hZP : Z ⊆ P := Finset.subset_union_right
  have hZQ : Z ⊆ Q := fun t ht => Finset.mem_sdiff.2 ⟨hZS ht, fun h => hKZ t h ht⟩
  have hcross : ∀ a b, G.Adj a b → (a ∈ P ∧ b ∈ P) ∨ (a ∈ Q ∧ b ∈ Q) := by
    intro a b hab
    have haS := hGS a b hab
    have hbS := hGS b a hab.symm
    simp only [P, Q, Finset.mem_union, Finset.mem_sdiff]
    by_cases haK : a ∈ K
    · left
      refine ⟨Or.inl haK, ?_⟩
      by_cases hbZ : b ∈ Z
      · exact Or.inr hbZ
      · exact Or.inl (hclos a b haK hbS hbZ hab)
    · by_cases hbK : b ∈ K
      · by_cases haZ : a ∈ Z
        · exact Or.inl ⟨Or.inr haZ, Or.inl hbK⟩
        · exact absurd (hclos b a hbK haS haZ hab.symm) haK
      · exact Or.inr ⟨⟨haS, haK⟩, ⟨hbS, hbK⟩⟩
  have hPcard : P.card < S.card := by
    refine Finset.card_lt_card ⟨fun t ht => hPQ ▸ Finset.mem_union_left _ ht, fun h => ?_⟩
    have := h ht₂
    simp only [P, Finset.mem_union] at this
    rcases this with h | h
    · exact ht₂K h
    · exact ht₂Z h
  have hQcard : Q.card < S.card := by
    refine Finset.card_lt_card ⟨Finset.sdiff_subset, fun h => ?_⟩
    have := h ht₁
    exact (Finset.mem_sdiff.1 this).2 ht₁K
  have ht₁P : t₁ ∈ P := Finset.mem_union_left _ ht₁K
  have ht₁Q : t₁ ∉ Q := fun h => (Finset.mem_sdiff.1 h).2 ht₁K
  have ht₂Q : t₂ ∈ Q := Finset.mem_sdiff.2 ⟨ht₂, ht₂K⟩
  have ht₂P : t₂ ∉ P := by
    simp only [P, Finset.mem_union, not_or]; exact ⟨ht₂K, ht₂Z⟩
  by_cases hAK : ∃ a ∈ A, a ∈ K
  · obtain ⟨a₀, ha₀A, ha₀K⟩ := hAK
    have hAP : A ⊆ P := by
      intro a ha
      by_contra haP
      simp only [P, Finset.mem_union, not_or] at haP
      have hne : a₀ ≠ a := fun h => haP.1 (h ▸ ha₀K)
      exact haP.1 (hclos a₀ a ha₀K (hAS ha) haP.2 (hAcl a₀ ha₀A a ha hne))
    exact ⟨P, Q, hPQ, hPQZ, hZP, hZQ, hcross, hAP, hPcard, hQcard,
      Or.inl ⟨ht₁P, ht₁Q, ht₂Q, ht₂P⟩⟩
  · push Not at hAK
    have hAQ : A ⊆ Q := fun a ha => Finset.mem_sdiff.2 ⟨hAS ha, hAK a ha⟩
    refine ⟨Q, P, by rw [Finset.union_comm]; exact hPQ, fun a h1 h2 => hPQZ a h2 h1, hZQ, hZP,
      fun a b hab => (hcross a b hab).symm, hAQ, hQcard, hPcard,
      Or.inr ⟨ht₂Q, ht₂P, ht₁P, ht₁Q⟩⟩

end LeanPool.K5MinorFreeChoosability
