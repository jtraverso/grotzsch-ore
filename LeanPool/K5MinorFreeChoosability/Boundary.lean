/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Lemma5

/-!
# Transport of `K_5`-minor-free boundaries

These are the minor-theoretic steps of the proof of Wood--Linusson, Lemma 7.  Each
statement shows that some apex extension is a minor of (or a clique-sum of minors of)
the apex extension `G^{B+α}` of the current graph, by exhibiting connected branch sets.

* `isK5Boundary_anti`: subgraphs and smaller boundaries;
* `isK5Boundary_singleton`: Case 1 (`∅` boundary to `{v}`), via a clique-sum;
* `isK5Boundary_delete`: Lemma 3 (contract the edge `vα`);
* `isK5Boundary_side`: Cases 5 and 6 (contract one side of a separation into `z`);
* `isK5Boundary_addEdge`: Case 6 (adding the edge `vw` across a 2-separation);
* `not_isK5Boundary_of_rootedK3`: Case 7 (a rooted `K_3` minor gives a `K_5` minor).
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*}

/-- `G` with the extra edge `vw` (if `v ≠ w`). -/
def addEdge (G : SimpleGraph V) (v w : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∨ (a ≠ b ∧ ((a = v ∧ b = w) ∨ (a = w ∧ b = v)))
  symm := ⟨fun _ _ h => by
    rcases h with h | ⟨hne, h⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hne.symm, by tauto⟩⟩
  loopless := ⟨fun _ h => by
    rcases h with h | ⟨hne, _⟩
    · exact G.irrefl h
    · exact hne rfl⟩

theorem le_addEdge (G : SimpleGraph V) (v w : V) : G ≤ addEdge G v w := fun _ _ h => Or.inl h

theorem addEdge_adj_self (G : SimpleGraph V) {v w : V} (h : v ≠ w) : (addEdge G v w).Adj v w :=
  Or.inr ⟨h, Or.inl ⟨rfl, rfl⟩⟩

theorem isK5Boundary_anti {G H : SimpleGraph V} {B B' : Set V} (hB : IsK5Boundary G B)
    (hH : H ≤ G) (hB' : B' ⊆ B) : IsK5Boundary H B' :=
  CliqueMinorFree.anti hB (apexExtend_mono hH hB')

theorem connSet_image_some [DecidableEq V] {G : SimpleGraph V} {B : Set V} {X : Finset V}
    (h : ConnSet G ↑X) : ConnSet (apexExtend G B) ↑(X.image some) := by
  obtain ⟨x, hx⟩ := h.1
  refine ⟨⟨some x, by simpa using hx⟩, ?_⟩
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  refine (h.2 a ha b hb).map some (fun p q hpq hp hq => ?_)
  exact RIn.single (by simpa using hpq) ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩

/-- **Case 1.**  If `∅` is a `K_5`-minor-free boundary, so is every singleton: the apex is
then a pendant vertex, glued along the clique `{v}`. -/
theorem isK5Boundary_singleton {G : SimpleGraph V} (h : IsK5Boundary G ∅) (v : V) :
    IsK5Boundary G {v} := by
  classical
  refine cliqueMinorFree_of_cliqueSum (by norm_num) (Set.range some) {none, some v} ?_ ?_ ?_ ?_
  · rintro (_ | a) (_ | b) hab
    · exact absurd hab id
    · simp only [apexExtend_none_some, Set.mem_singleton_iff] at hab
      subst hab; right; simp
    · simp only [apexExtend_some_none, Set.mem_singleton_iff] at hab
      subst hab; right; simp
    · left; exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  · rintro a ⟨⟨a', rfl⟩, ha⟩ b ⟨⟨b', rfl⟩, hb⟩ hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, reduceCtorEq, false_or,
      Option.some.injEq] at ha hb
    subst ha; subst hb; exact absurd rfl hab
  · refine CliqueMinorFree.anti h ?_
    rintro (_ | a) (_ | b) ⟨hab, ha, hb⟩
    · exact hab
    · obtain ⟨_, h⟩ := ha; simp at h
    · obtain ⟨_, h⟩ := hb; simp at h
    · exact hab
  · refine cliqueMinorFree_of_edges_subset (by norm_num) {none, some v} ?_ ?_
    · rintro a b ⟨_, ha, _⟩
      simpa using ha
    · exact lt_of_le_of_lt (Finset.card_le_two) (by norm_num)

/-- **Lemma 3.**  Deleting a boundary vertex `v`, the set `(B \ {v}) ∪ N(v)` (or any
subset of it) is a boundary of the remaining graph: contract the edge `vα`. -/
theorem isK5Boundary_delete {G : SimpleGraph V} {B B' : Set V} {s : Set V} {v : V}
    (hB : IsK5Boundary G B) (hvB : v ∈ B) (hvs : v ∉ s)
    (hB' : ∀ u ∈ B', (u ∈ B ∧ u ≠ v) ∨ G.Adj v u) :
    IsK5Boundary (restrict G s) B' := by
  classical
  refine cliqueMinorFree_of_transport (by norm_num) {x | x ≠ some v} ?_
    (fun x => if x = none then {none, some v} else {x}) ?_ ?_ ?_ hB
  · rintro (_ | a) (_ | b) hab
    · exact absurd hab id
    · simp
    · simp only [apexExtend_some_none] at hab
      rcases hB' a hab with h | h
      · simpa using h.2
      · simpa using (G.ne_of_adj h).symm
    · simp only [apexExtend_some_some, restrict_adj] at hab
      simp only [ne_eq, Set.mem_ofPred_eq, Option.some.injEq]
      rintro rfl; exact hvs hab.2.1
  · rintro (_ | a) _
    · simp only [↓reduceIte, Finset.coe_insert, Finset.coe_singleton]
      exact (connSet_singleton _ _).insert_adj rfl (by simpa using hvB)
    · simpa using connSet_singleton _ _
  · rintro (_ | a) ha (_ | b) hb hab
    · exact absurd rfl hab
    · simp only [Set.mem_ofPred_eq, ne_eq, Option.some.injEq] at hb
      simp [hb]
    · simp only [Set.mem_ofPred_eq, ne_eq, Option.some.injEq] at ha
      simp [ha]
    · simpa using hab
  · rintro (_ | a) (_ | b) hab
    · exact absurd hab id
    · simp only [apexExtend_none_some] at hab
      rcases hB' b hab with h | h
      · exact ⟨none, by simp, some b, by simp, by simpa using h.1⟩
      · exact ⟨some v, by simp, some b, by simp, by simpa using h⟩
    · simp only [apexExtend_some_none] at hab
      rcases hB' a hab with h | h
      · exact ⟨some a, by simp, none, by simp, by simpa using h.1⟩
      · exact ⟨some a, by simp, some v, by simp, by simpa using h.symm⟩
    · simp only [apexExtend_some_some, restrict_adj] at hab
      exact ⟨some a, by simp, some b, by simp, by simpa using hab.1⟩

/-- In a separation `(S₁, S₂)` of `G`, a vertex `b ∈ S₁ \ S₂` joined to `z` by a path
avoiding the other separator vertices has a connected neighbourhood in `S₁ \ S₂`
adjacent to `z`. -/
theorem exists_side_component {G : SimpleGraph V} {S₁ S₂ : Finset V}
    (hcross : ∀ a b, G.Adj a b → (a ∈ S₁ ∧ b ∈ S₁) ∨ (a ∈ S₂ ∧ b ∈ S₂))
    {s : Set V} {z b : V} (hs : ∀ t ∈ s, t ∈ S₁ → t ∈ S₂ → t = z) (hz : z ∈ S₂)
    (hb₁ : b ∈ S₁) (hb₂ : b ∉ S₂) (hpath : RIn G s b z) :
    ∃ p, p ∈ S₁ ∧ p ∉ S₂ ∧ RIn G (↑S₁ \ ↑S₂) b p ∧ G.Adj p z := by
  obtain ⟨p, q, hbp, hps, hpP, hqs, hqP, hpq⟩ :=
    hpath.exit (P := ↑S₁ \ ↑S₂) ⟨hb₁, hb₂⟩ (fun h => h.2 hz)
  have hq₁ : q ∈ S₁ := by
    rcases hcross p q hpq with h | h
    · exact h.2
    · exact absurd h.1 hpP.2
  have hq₂ : q ∈ S₂ := by
    by_contra h
    exact hqP ⟨hq₁, h⟩
  obtain rfl := hs q hqs hq₁ hq₂
  exact ⟨p, hpP.1, hpP.2, hbp.mono_set Set.inter_subset_right, hpq⟩

/-- The component of `b` inside `S₁ \ S₂`, as a finite set. -/
noncomputable def sideComp (G : SimpleGraph V) (S₁ S₂ : Finset V) (b : V) : Finset V := by
  classical
  exact S₁.filter (fun t => t ∉ S₂ ∧ RIn G (↑S₁ \ ↑S₂) b t)

theorem mem_sideComp {G : SimpleGraph V} {S₁ S₂ : Finset V} {b t : V} :
    t ∈ sideComp G S₁ S₂ b ↔ t ∈ S₁ ∧ t ∉ S₂ ∧ RIn G (↑S₁ \ ↑S₂) b t := by
  classical
  simp [sideComp]

theorem connSet_sideComp {G : SimpleGraph V} {S₁ S₂ : Finset V} {b : V} (hb₁ : b ∈ S₁)
    (hb₂ : b ∉ S₂) : ConnSet G ↑(sideComp G S₁ S₂ b) := by
  have h := connSet_reach G (↑S₁ \ ↑S₂) (a := b) ⟨hb₁, hb₂⟩
  have heq : (↑(sideComp G S₁ S₂ b) : Set V) =
      {x | x ∈ (↑S₁ \ ↑S₂ : Set V) ∧ RIn G (↑S₁ \ ↑S₂) b x} := by
    ext t
    rw [Finset.mem_coe, mem_sideComp]
    exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩
  rw [heq]; exact h

/-- **Cases 5 and 6.**  Contracting the part of side `S₁` around `b` into the separator
vertex `z` shows that `(B ∩ S₂) ∪ {z}` is a boundary of `G[S₂]`. -/
theorem isK5Boundary_side {G : SimpleGraph V} {B : Set V} {S₁ S₂ : Finset V}
    (hB : IsK5Boundary G B)
    (hcross : ∀ a b, G.Adj a b → (a ∈ S₁ ∧ b ∈ S₁) ∨ (a ∈ S₂ ∧ b ∈ S₂))
    {s : Set V} {z b : V} (hs : ∀ t ∈ s, t ∈ S₁ → t ∈ S₂ → t = z) (hz : z ∈ S₂)
    (hb₁ : b ∈ S₁) (hb₂ : b ∉ S₂) (hbB : b ∈ B) (hpath : RIn G s b z)
    {B₂ : Set V} (hB₂ : ∀ u ∈ B₂, u ∈ S₂ ∧ (u ∈ B ∨ u = z)) :
    IsK5Boundary (restrict G ↑S₂) B₂ := by
  classical
  obtain ⟨p, hp₁, hp₂, hbp, hpz⟩ := exists_side_component hcross hs hz hb₁ hb₂ hpath
  set K := sideComp G S₁ S₂ b with hK
  have hpK : p ∈ K := mem_sideComp.2 ⟨hp₁, hp₂, hbp⟩
  have hbK : b ∈ K := mem_sideComp.2 ⟨hb₁, hb₂, RIn.refl _⟩
  have hKS₂ : ∀ t ∈ K, t ∉ S₂ := fun t ht => (mem_sideComp.1 ht).2.1
  have hconn : ConnSet G ↑(insert z K) := by
    rw [Finset.coe_insert]
    exact (connSet_sideComp hb₁ hb₂).insert_adj hpK hpz.symm
  let φ : Option V → Finset (Option V) := fun x =>
    if x = some z then (insert z K).image some else {x}
  have hself : ∀ x, x ∈ φ x := by
    intro x
    by_cases hx : x = some z
    · subst hx; simp [φ]
    · simp [φ, hx]
  refine cliqueMinorFree_of_transport (by norm_num) ({none} ∪ (some '' ↑S₂)) ?_ φ ?_ ?_ ?_ hB
  · rintro (_ | a) (_ | b) hab
    · exact absurd hab id
    · simp
    · simp only [apexExtend_some_none] at hab
      simpa using (hB₂ a hab).1
    · simp only [apexExtend_some_some, restrict_adj] at hab
      simpa using hab.2.1
  · rintro x -
    by_cases hx : x = some z
    · subst hx; simpa [φ] using connSet_image_some hconn
    · simpa [φ, hx] using connSet_singleton _ x
  · rintro x hx y hy hxy
    have key : ∀ y, y ∈ ({none} ∪ (some '' ↑S₂) : Set (Option V)) → y ≠ some z →
        Disjoint ((insert z K).image some) {y} := by
      rintro (_ | y) hy hyz
      · simp
      · simp only [Set.mem_union, Set.mem_singleton_iff, reduceCtorEq, Set.mem_image,
          Finset.mem_coe, Option.some.injEq, exists_eq_right, false_or] at hy
        simp only [ne_eq, Option.some.injEq] at hyz
        simp only [Finset.disjoint_singleton_right, Finset.mem_image, Finset.mem_insert,
          Option.some.injEq, exists_eq_right, not_or]
        exact ⟨hyz, fun h => hKS₂ y h hy⟩
    by_cases hxz : x = some z
    · subst hxz
      simpa [φ, Ne.symm hxy] using key y hy (Ne.symm hxy)
    · by_cases hyz : y = some z
      · subst hyz
        simpa [φ, hxy] using (key x hx hxz).symm
      · simpa [φ, hxz, hyz] using hxy
  · rintro (_ | a) (_ | c) hac
    · exact absurd hac id
    · simp only [apexExtend_none_some] at hac
      rcases (hB₂ c hac).2 with h | rfl
      · exact ⟨none, hself _, some c, hself _, by simpa using h⟩
      · exact ⟨none, hself _, some b, by simp [φ, hbK], by simpa using hbB⟩
    · simp only [apexExtend_some_none] at hac
      rcases (hB₂ a hac).2 with h | rfl
      · exact ⟨some a, hself _, none, hself _, by simpa using h⟩
      · exact ⟨some b, by simp [φ, hbK], none, hself _, by simpa using hbB⟩
    · simp only [apexExtend_some_some, restrict_adj] at hac
      exact ⟨some a, hself _, some c, hself _, by simpa using hac.1⟩

/-- `H` together with all edges between distinct vertices of `Z`. -/
def withClique {W : Type*} (H : SimpleGraph W) (Z : Set W) : SimpleGraph W where
  Adj a b := H.Adj a b ∨ (a ≠ b ∧ a ∈ Z ∧ b ∈ Z)
  symm := ⟨fun _ _ h => by
    rcases h with h | ⟨hne, ha, hb⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hne.symm, hb, ha⟩⟩
  loopless := ⟨fun _ h => by
    rcases h with h | ⟨hne, _⟩
    · exact H.irrefl h
    · exact hne rfl⟩

/-- One side of the clique-sum used in Case 6: the side `S₁` of the separation, with the
triangle `{α, v, w}` added, is a minor of `G^{B+α}`.  The triangle is realised by
contracting into `w` the component `K` of the other side, which contains a vertex of `B`
and is adjacent to both `v` and `w`. -/
theorem addEdge_side_free {G : SimpleGraph V} {B : Set V} {S₁ S₂ : Finset V} {v w b p p' : V}
    (hB : IsK5Boundary G B) (hvB : v ∈ B)
    (hbB : b ∈ B) (hb₂ : b ∈ S₂) (hb₁ : b ∉ S₁)
    (hp : p ∈ sideComp G S₂ S₁ b) (hp' : p' ∈ sideComp G S₂ S₁ b)
    (hpw : G.Adj p w) (hp'v : G.Adj p' v) :
    CliqueMinorFree (restrict (withClique (apexExtend (addEdge G v w) B)
      {none, some v, some w}) ({none} ∪ some '' ↑S₁)) 5 := by
  classical
  set K := sideComp G S₂ S₁ b with hK
  have hbK : b ∈ K := mem_sideComp.2 ⟨hb₂, hb₁, RIn.refl _⟩
  have hKS₁ : ∀ t ∈ K, t ∉ S₁ := fun t ht => (mem_sideComp.1 ht).2.1
  have hconn : ConnSet G ↑(insert w K) := by
    rw [Finset.coe_insert]
    exact (connSet_sideComp hb₂ hb₁).insert_adj hp hpw.symm
  let φ : Option V → Finset (Option V) := fun x =>
    if x = some w then (insert w K).image some else {x}
  have hself : ∀ x, x ∈ φ x := by
    intro x
    by_cases hx : x = some w
    · subst hx; simp [φ]
    · simp [φ, hx]
  have hwK : ∀ c ∈ insert w K, some c ∈ φ (some w) := by
    intro c hc; simp only [φ, ↓reduceIte, Finset.mem_image]; exact ⟨c, hc, rfl⟩
  have hpK : some p' ∈ φ (some w) := hwK p' (Finset.mem_insert_of_mem hp')
  have hbK' : some b ∈ φ (some w) := hwK b (Finset.mem_insert_of_mem hbK)
  refine cliqueMinorFree_of_transport (by norm_num) ({none} ∪ some '' ↑S₁) ?_ φ ?_ ?_ ?_ hB
  · rintro a b ⟨_, ha, _⟩; exact ha
  · rintro x -
    by_cases hx : x = some w
    · subst hx; simpa [φ] using connSet_image_some hconn
    · simpa [φ, hx] using connSet_singleton _ x
  · rintro x hx y hy hxy
    have key : ∀ y, y ∈ ({none} ∪ (some '' ↑S₁) : Set (Option V)) → y ≠ some w →
        Disjoint ((insert w K).image some) {y} := by
      rintro (_ | y) hy hyw
      · simp
      · simp only [Set.mem_union, Set.mem_singleton_iff, reduceCtorEq, Set.mem_image,
          Finset.mem_coe, Option.some.injEq, exists_eq_right, false_or] at hy
        simp only [ne_eq, Option.some.injEq] at hyw
        simp only [Finset.disjoint_singleton_right, Finset.mem_image, Finset.mem_insert,
          Option.some.injEq, exists_eq_right, not_or]
        exact ⟨hyw, fun h => hKS₁ y h hy⟩
    by_cases hxw : x = some w
    · subst hxw
      simpa [φ, Ne.symm hxy] using key y hy (Ne.symm hxy)
    · by_cases hyw : y = some w
      · subst hyw
        simpa [φ, hxy] using (key x hx hxw).symm
      · simpa [φ, hxw, hyw] using hxy
  · rintro x y ⟨hxy, -, -⟩
    rcases hxy with hxy | ⟨hne, hx, hy⟩
    · rcases x with _ | a <;> rcases y with _ | c
      · exact absurd hxy id
      · exact ⟨none, hself _, some c, hself _, hxy⟩
      · exact ⟨some a, hself _, none, hself _, hxy⟩
      · rcases hxy with h | ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact ⟨some a, hself _, some c, hself _, h⟩
        · exact ⟨some a, hself _, some p', hpK, hp'v.symm⟩
        · exact ⟨some p', hpK, some c, hself _, hp'v⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact absurd rfl hne
      · exact ⟨none, hself _, some v, hself _, hvB⟩
      · exact ⟨none, hself _, some b, hbK', hbB⟩
      · exact ⟨some v, hself _, none, hself _, hvB⟩
      · exact absurd rfl hne
      · exact ⟨some v, hself _, some p', hpK, hp'v.symm⟩
      · exact ⟨some b, hbK', none, hself _, hbB⟩
      · exact ⟨some p', hpK, some v, hself _, hp'v⟩
      · exact absurd rfl hne

/-- **Case 6, edge insertion.**  Let `{S₁, S₂}` be a separation of `G` with
`S₁ ∩ S₂ = {v, w}` (as far as the vertices carrying edges or in `B` are concerned) and
`v ∈ B`.  If each side `Sᵢ` contains a vertex `bᵢ ∈ B \ S_{3-i}` whose component in
`Sᵢ \ S_{3-i}` is adjacent to both `v` and `w`, then adding the edge `vw` keeps `B` a
`K_5`-minor-free boundary. -/
theorem isK5Boundary_addEdge {G : SimpleGraph V} {B : Set V} {S₁ S₂ : Finset V} {v w : V}
    (hB : IsK5Boundary G B)
    (hcross : ∀ a b, G.Adj a b → (a ∈ S₁ ∧ b ∈ S₁) ∨ (a ∈ S₂ ∧ b ∈ S₂))
    (hBS : ∀ b ∈ B, b ∈ S₁ ∨ b ∈ S₂)
    (hZ : ∀ t, t ∈ S₁ → t ∈ S₂ → t = v ∨ t = w)
    (hv₁ : v ∈ S₁) (hv₂ : v ∈ S₂) (hw₁ : w ∈ S₁) (hw₂ : w ∈ S₂) (hvB : v ∈ B)
    {b₁ p₁ p₁' b₂ p₂ p₂' : V}
    (hb₁B : b₁ ∈ B) (hb₁₁ : b₁ ∈ S₁) (hb₁₂ : b₁ ∉ S₂)
    (hp₁ : p₁ ∈ sideComp G S₁ S₂ b₁) (hp₁' : p₁' ∈ sideComp G S₁ S₂ b₁)
    (hp₁w : G.Adj p₁ w) (hp₁'v : G.Adj p₁' v)
    (hb₂B : b₂ ∈ B) (hb₂₂ : b₂ ∈ S₂) (hb₂₁ : b₂ ∉ S₁)
    (hp₂ : p₂ ∈ sideComp G S₂ S₁ b₂) (hp₂' : p₂' ∈ sideComp G S₂ S₁ b₂)
    (hp₂w : G.Adj p₂ w) (hp₂'v : G.Adj p₂' v) :
    IsK5Boundary (addEdge G v w) B := by
  refine CliqueMinorFree.anti (H := apexExtend (addEdge G v w) B)
    (G := withClique (apexExtend (addEdge G v w) B) {none, some v, some w}) ?_
    (fun _ _ h => Or.inl h)
  refine cliqueMinorFree_of_cliqueSum (by norm_num) ({none} ∪ some '' ↑S₁)
    ({none} ∪ some '' ↑S₂) ?_ ?_
    (addEdge_side_free hB hvB hb₂B hb₂₂ hb₂₁ hp₂ hp₂' hp₂w hp₂'v)
    (addEdge_side_free hB hvB hb₁B hb₁₁ hb₁₂ hp₁ hp₁' hp₁w hp₁'v)
  · rintro x y hxy
    rcases hxy with hxy | ⟨_, hx, hy⟩
    · rcases x with _ | a <;> rcases y with _ | c
      · exact absurd hxy id
      · rcases hBS c hxy with h | h
        · left; simp [h]
        · right; simp [h]
      · rcases hBS a hxy with h | h
        · left; simp [h]
        · right; simp [h]
      · rcases hxy with h | ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · rcases hcross a c h with h | h
          · left; simp [h.1, h.2]
          · right; simp [h.1, h.2]
        · left; simp [hv₁, hw₁]
        · left; simp [hv₁, hw₁]
    · left
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      constructor
      · rcases hx with rfl | rfl | rfl <;> simp [hv₁, hw₁]
      · rcases hy with rfl | rfl | rfl <;> simp [hv₁, hw₁]
  · rintro x hx y hy hxy
    have hmem : ∀ t ∈ ({none} ∪ some '' ↑S₁ : Set (Option V)) ∩ ({none} ∪ some '' ↑S₂),
        t ∈ ({none, some v, some w} : Set (Option V)) := by
      rintro (_ | t) ⟨ht₁, ht₂⟩
      · simp
      · simp only [Set.mem_union, Set.mem_singleton_iff, reduceCtorEq, Set.mem_image,
          Finset.mem_coe, Option.some.injEq, exists_eq_right, false_or] at ht₁ ht₂
        rcases hZ t ht₁ ht₂ with rfl | rfl <;> simp
    exact Or.inr ⟨hxy, hmem x hx, hmem y hy⟩

/-- **Case 7.**  If `v ∈ B` has three neighbours `x, y, z ∈ B` and `G[S] - v` has a `K_3`
minor rooted at `x, y, z`, then together with `v` and the apex this gives a `K_5` minor of
`G^{B+α}`. -/
theorem not_isK5Boundary_of_rootedK3 [DecidableEq V] {G : SimpleGraph V} {B : Set V}
    {S : Finset V} {v x y z : V} (hvB : v ∈ B) (hxB : x ∈ B) (hyB : y ∈ B) (hzB : z ∈ B)
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hvz : G.Adj v z)
    (h : RootedK3 G (S.erase v) x y z) : ¬ IsK5Boundary G B := by
  obtain ⟨X, Y, Z, hXS, hYS, hZS, hx, hy, hz, hcX, hcY, hcZ, hXY, hYZ, hXZ,
    ⟨a1, ha1, b1, hb1, h1⟩, ⟨a2, ha2, b2, hb2, h2⟩, ⟨a3, ha3, b3, hb3, h3⟩⟩ := h
  have hvX : v ∉ X := fun h => by simpa using hXS h
  have hvY : v ∉ Y := fun h => by simpa using hYS h
  have hvZ : v ∉ Z := fun h => by simpa using hZS h
  intro hB
  apply hB
  let br : Fin 5 → Finset (Option V) :=
    ![X.image some, Y.image some, Z.image some, {some v}, {none}]
  have hadj : ∀ i j : Fin 5, i < j → ∃ u ∈ br i, ∃ w ∈ br j, (apexExtend G B).Adj u w := by
    intro i j hij
    have mi : ∀ {a : V} {T : Finset V}, a ∈ T → some a ∈ T.image some :=
      fun h => Finset.mem_image_of_mem _ h
    fin_cases i <;> fin_cases j <;> simp at hij <;>
      first
      | exact ⟨some a1, mi ha1, some b1, mi hb1, h1⟩
      | exact ⟨some a2, mi ha2, some b2, mi hb2, h2⟩
      | exact ⟨some a3, mi ha3, some b3, mi hb3, h3⟩
      | exact ⟨some x, mi hx, some v, Finset.mem_singleton_self _, hvx.symm⟩
      | exact ⟨some y, mi hy, some v, Finset.mem_singleton_self _, hvy.symm⟩
      | exact ⟨some z, mi hz, some v, Finset.mem_singleton_self _, hvz.symm⟩
      | exact ⟨some x, mi hx, none, Finset.mem_singleton_self _, hxB⟩
      | exact ⟨some y, mi hy, none, Finset.mem_singleton_self _, hyB⟩
      | exact ⟨some z, mi hz, none, Finset.mem_singleton_self _, hzB⟩
      | exact ⟨some v, Finset.mem_singleton_self _, none, Finset.mem_singleton_self _, hvB⟩
  refine ⟨CliqueMinorModel.ofConnSet br (fun i => ?_) (fun i j hij => ?_) (fun i j hij => ?_)⟩
  · fin_cases i
    · exact connSet_image_some hcX
    · exact connSet_image_some hcY
    · exact connSet_image_some hcZ
    · simpa [br] using connSet_singleton _ (some v)
    · simpa [br] using connSet_singleton _ none
  · have nX : some v ∉ X.image some := by simpa using hvX
    have nY : some v ∉ Y.image some := by simpa using hvY
    have nZ : some v ∉ Z.image some := by simpa using hvZ
    have mX : none ∉ X.image some := by simp
    have mY : none ∉ Y.image some := by simp
    have mZ : none ∉ Z.image some := by simp
    have mv : none ∉ ({some v} : Finset (Option V)) := by simp
    fin_cases i <;> fin_cases j <;> simp at hij <;>
      first
      | exact (Finset.disjoint_image (Option.some_injective V)).2 hXY
      | exact (Finset.disjoint_image (Option.some_injective V)).2 hYZ
      | exact (Finset.disjoint_image (Option.some_injective V)).2 hXZ
      | exact (Finset.disjoint_image (Option.some_injective V)).2 hXY.symm
      | exact (Finset.disjoint_image (Option.some_injective V)).2 hYZ.symm
      | exact (Finset.disjoint_image (Option.some_injective V)).2 hXZ.symm
      | exact Finset.disjoint_singleton_right.2 nX
      | exact Finset.disjoint_singleton_right.2 nY
      | exact Finset.disjoint_singleton_right.2 nZ
      | exact Finset.disjoint_singleton_left.2 nX
      | exact Finset.disjoint_singleton_left.2 nY
      | exact Finset.disjoint_singleton_left.2 nZ
      | exact Finset.disjoint_singleton_right.2 mX
      | exact Finset.disjoint_singleton_right.2 mY
      | exact Finset.disjoint_singleton_right.2 mZ
      | exact Finset.disjoint_singleton_left.2 mX
      | exact Finset.disjoint_singleton_left.2 mY
      | exact Finset.disjoint_singleton_left.2 mZ
      | exact Finset.disjoint_singleton_right.2 mv
      | exact Finset.disjoint_singleton_left.2 mv
  · rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact hadj i j hlt
    · obtain ⟨u, hu, w, hw, huw⟩ := hadj j i hlt
      exact ⟨w, hw, u, hu, huw.symm⟩

end LeanPool.K5MinorFreeChoosability
