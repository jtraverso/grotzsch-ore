/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Grotzsch.PlusEdge

/-!
# Precolouring extension for 4- and 5-cycles

**Theorem (BKLY 2014, Theorem 5, for cycles of length 4 and 5).** Let `G` be a triangle-free
planar graph and `C` a cycle of `G` of length 4 or 5. Every proper 3-colouring of the cycle `C`
extends to a 3-colouring of `G`.

In the paper `C` is a face; here it is any cycle, and no faces are needed. A proper 3-colouring
of a 4- or 5-cycle is determined, up to a permutation of the colours, by its pattern of equal
colours, and a gadget forces that pattern:
* a 4-cycle `a b c d` coloured with two colours: a new vertex adjacent to `a, b, c, d`
  (BKLY Theorem 4, `colorable_of_induce_planar_cliqueFree`);
* a 4-cycle `a b c d` with `a, c` equal and `b, d` different: the chord `bd`
  (BKLY Theorem 2, `colorable_of_sdiff_edge`);
* a 5-cycle `a b c d e` coloured `x y x y z`: a new vertex adjacent to `a, b, c, d`
  (BKLY Theorem 4).
Theorem 4 does not need the graph with the new vertex to be planar, so the cycle need not bound
a face.
-/

@[expose] public section

noncomputable section

open Classical Finset Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

namespace Grotzsch

/-! ### Colour permutations -/

/-- Two maps to `Fin 3` with the same pattern of equalities differ by a permutation. -/
theorem exists_perm_of_pattern {ι : Type*} (f φ : ι → Fin 3)
    (h : ∀ i j, f i = f j ↔ φ i = φ j) : ∃ π : Perm (Fin 3), ∀ i, π (f i) = φ i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, fun i => isEmptyElim i⟩
  let g : Fin 3 → Fin 3 := fun a => φ (Function.invFun f a)
  have hg : ∀ i, g (f i) = φ i := fun i =>
    (h _ _).1 (Function.invFun_eq (f := f) ⟨i, rfl⟩)
  have hinj : Set.InjOn g (Set.range f) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    rw [hg, hg] at hij
    exact (h i j).2 hij
  obtain ⟨e, he⟩ := Set.MapsTo.exists_equiv_extend_of_card_eq (t := Finset.univ)
    (by simp) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
  refine ⟨e.trans (Equiv.subtypeUnivEquiv fun _ => Finset.mem_univ _), fun i => ?_⟩
  simp [he (f i) ⟨i, rfl⟩, hg]

variable {V : Type} [Fintype V] {G : SimpleGraph V}

/-- Recolouring a colouring by a permutation of the colours. -/
def recolour (f : G.Coloring (Fin 3)) (π : Perm (Fin 3)) : G.Coloring (Fin 3) :=
  SimpleGraph.Coloring.mk (fun v => π (f v)) fun h e => f.valid h (π.injective e)

omit [Fintype V] in
@[simp] theorem recolour_apply (f : G.Coloring (Fin 3)) (π : Perm (Fin 3)) (v : V) :
    recolour f π v = π (f v) := rfl

/-! ### The gadgets -/

/-- **BKLY Theorem 4, apex form.** A new vertex adjacent to at most four vertices of a
triangle-free planar graph keeps it 3-colourable. -/
theorem colorable_apexExtend (hP : IsPlanar G) (h3 : G.CliqueFree 3) {S : Finset V}
    (hS : S.card ≤ 4) : (apexExtend G (S : Set V)).Colorable 3 := by
  set H := apexExtend G (S : Set V) with hH
  let f : {w : Option V // w ∈ {w | w ≠ none}} → V := fun w =>
    w.1.get (Option.ne_none_iff_isSome.1 w.2)
  have hf : Function.Injective f := by
    rintro ⟨_ | x, hx⟩ ⟨_ | y, hy⟩ hxy
    · exact absurd rfl hx
    · exact absurd rfl hx
    · exact absurd rfl hy
    · simp only [f, Option.get_some] at hxy
      subst hxy; rfl
  have hadj : ∀ a b, (H.induce {w | w ≠ none}).Adj a b → G.Adj (f a) (f b) := by
    rintro ⟨_ | x, hx⟩ ⟨_ | y, hy⟩ hab
    · exact absurd rfl hx
    · exact absurd rfl hx
    · exact absurd rfl hy
    · exact hab
  obtain ⟨hP', h3'⟩ := planar_cliqueFree_of_injective f hf hadj
  refine colorable_of_induce_planar_cliqueFree H none (hP' hP) (h3' h3) ?_
  have hsub : H.neighborFinset none ⊆ S.image some := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    rcases w with _ | x
    · exact absurd hw (by simp [hH, apexExtend])
    · exact Finset.mem_image.2 ⟨x, by simpa [hH, apexExtend] using hw, rfl⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans hS)

/-- A colouring of the graph with an apex restricts to a colouring of the graph. -/
def restrictApex {S : Set V} (F : (apexExtend G S).Coloring (Fin 3)) : G.Coloring (Fin 3) :=
  SimpleGraph.Coloring.mk (fun v => F (some v)) fun h => F.valid h

omit [Fintype V] in
theorem ne_apex {S : Set V} (F : (apexExtend G S).Coloring (Fin 3)) {x : V} (hx : x ∈ S) :
    restrictApex F x ≠ F none :=
  F.valid (show (apexExtend G S).Adj (some x) none from hx)

/-- Two vertices of `Fin 3` both avoiding `w` and both different from `y` are equal. -/
theorem fin3_eq_of_ne {x y z w : Fin 3} (hxw : x ≠ w) (hyw : y ≠ w) (hzw : z ≠ w) (hxy : x ≠ y)
    (hyz : y ≠ z) : x = z := by
  revert x y z w; decide

theorem fin3_eq_of_ne' {x y z w : Fin 3} (hxy : x ≠ y) (hxw : x ≠ w) (hzy : z ≠ y) (hzw : z ≠ w)
    (hyw : y ≠ w) : x = z := by
  revert x y z w; decide

/-- A 4-cycle `a b c d` can be coloured with `a, c` and `b, d` equal. -/
theorem exists_coloring_four_two (hP : IsPlanar G) (h3 : G.CliqueFree 3) {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) :
    ∃ f : G.Coloring (Fin 3), f a = f c ∧ f b = f d ∧ f a ≠ f b := by
  obtain ⟨F⟩ := colorable_apexExtend hP h3 (S := {a, b, c, d}) Finset.card_le_four
  set f := restrictApex F
  have ha := ne_apex F (x := a) (by simp)
  have hb := ne_apex F (x := b) (by simp)
  have hc := ne_apex F (x := c) (by simp)
  have hd := ne_apex F (x := d) (by simp)
  exact ⟨f, fin3_eq_of_ne ha hb hc (f.valid hab) (f.valid hbc),
    fin3_eq_of_ne hb hc hd (f.valid hbc) (f.valid hcd), f.valid hab⟩

/-- A 4-cycle `a b c d` can be coloured with `a, c` equal and `b, d` different. -/
theorem exists_coloring_four_three (hP : IsPlanar G) (h3 : G.CliqueFree 3) {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) (hbd : b ≠ d) :
    ∃ f : G.Coloring (Fin 3), f a = f c ∧ f b ≠ f d := by
  set H := G ⊔ SimpleGraph.edge b d with hH
  have hadj : ∀ x y, (H.deleteEdges {s(b, d)}).Adj x y → G.Adj (id x) (id y) := by
    intro x y hxy
    rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at hxy
    obtain ⟨h | h, hne⟩ := hxy
    · exact h
    · exfalso
      rw [SimpleGraph.edge_adj] at h
      rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne rfl
      · exact hne Sym2.eq_swap
  obtain ⟨hP', h3'⟩ := planar_cliqueFree_of_injective id Function.injective_id hadj
  obtain ⟨F⟩ := colorable_of_sdiff_edge H hbd (hP' hP) (h3' h3)
  let f : G.Coloring (Fin 3) :=
    SimpleGraph.Coloring.mk (fun v => F v) fun h => F.valid (Or.inl h)
  have hFbd : F b ≠ F d := F.valid (Or.inr (by rw [SimpleGraph.edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, hbd⟩))
  exact ⟨f, fin3_eq_of_ne' (f.valid hab) (f.valid hda.symm) (f.valid hbc.symm) (f.valid hcd)
    hFbd, hFbd⟩

/-- A 5-cycle `a b c d e` can be coloured `x y x y z`. -/
theorem exists_coloring_five (hP : IsPlanar G) (h3 : G.CliqueFree 3) {a b c d e : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e) (hea : G.Adj e a) :
    ∃ f : G.Coloring (Fin 3), f a = f c ∧ f b = f d ∧ f a ≠ f b ∧ f e ≠ f a ∧ f e ≠ f b := by
  obtain ⟨F⟩ := colorable_apexExtend hP h3 (S := {a, b, c, d}) Finset.card_le_four
  set f := restrictApex F
  have ha := ne_apex F (x := a) (by simp)
  have hb := ne_apex F (x := b) (by simp)
  have hc := ne_apex F (x := c) (by simp)
  have hd := ne_apex F (x := d) (by simp)
  have hbd := fin3_eq_of_ne hb hc hd (f.valid hbc) (f.valid hcd)
  refine ⟨f, fin3_eq_of_ne ha hb hc (f.valid hab) (f.valid hbc), hbd, f.valid hab,
    f.valid hea, ?_⟩
  rw [hbd]
  exact f.valid hde.symm

/-! ### Patterns of proper colourings of short cycles -/

theorem zmod4_cases : ∀ i r : ZMod 4, i = r ∨ i = r + 1 ∨ i = r + 2 ∨ i = r + 3 := by decide

theorem zmod5_cases : ∀ i r : ZMod 5,
    i = r ∨ i = r + 1 ∨ i = r + 2 ∨ i = r + 3 ∨ i = r + 4 := by decide

/-- A proper 3-colouring of a 4-cycle uses two colours, or has exactly one pair of equal
opposite vertices. -/
theorem pattern_four (φ : ZMod 4 → Fin 3) (hφ : ∀ i, φ i ≠ φ (i + 1)) :
    (φ 0 = φ 2 ∧ φ 1 = φ 3) ∨ ∃ r, φ r = φ (r + 2) ∧ φ (r + 1) ≠ φ (r + 3) := by
  have key : ∀ a b c d : Fin 3, a ≠ b → b ≠ c → c ≠ d → d ≠ a →
      (a = c ∧ b = d) ∨ (a = c ∧ b ≠ d) ∨ (b = d ∧ c ≠ a) := by decide
  rcases key (φ 0) (φ 1) (φ 2) (φ 3) (hφ 0) (hφ 1) (hφ 2) (hφ 3) with h | h | h
  · exact Or.inl h
  · exact Or.inr ⟨0, h.1, h.2⟩
  · exact Or.inr ⟨1, h.1, h.2⟩

/-- A proper 3-colouring of a 5-cycle is `x y x y z` up to rotation. -/
theorem pattern_five (φ : ZMod 5 → Fin 3) (hφ : ∀ i, φ i ≠ φ (i + 1)) :
    ∃ r, φ r = φ (r + 2) ∧ φ (r + 1) = φ (r + 3) := by
  have key : ∀ a b c d e : Fin 3, a ≠ b → b ≠ c → c ≠ d → d ≠ e → e ≠ a →
      (a = c ∧ b = d) ∨ (b = d ∧ c = e) ∨ (c = e ∧ d = a) ∨ (d = a ∧ e = b) ∨
        (e = b ∧ a = c) := by decide
  rcases key (φ 0) (φ 1) (φ 2) (φ 3) (φ 4) (hφ 0) (hφ 1) (hφ 2) (hφ 3) (hφ 4) with
    h | h | h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩
  · exact ⟨3, h⟩
  · exact ⟨4, h⟩

/-! ### Precolouring extension -/

/-- **Precolouring extension for 4-cycles.** In a triangle-free planar graph, every proper
3-colouring of a 4-cycle extends to the whole graph. -/
theorem exists_coloring_extend_four (hP : IsPlanar G) (h3 : G.CliqueFree 3) {c : ZMod 4 → V}
    (hinj : Function.Injective c) (hadj : ∀ i, G.Adj (c i) (c (i + 1))) (φ : ZMod 4 → Fin 3)
    (hφ : ∀ i, φ i ≠ φ (i + 1)) : ∃ f : G.Coloring (Fin 3), ∀ i, f (c i) = φ i := by
  have key : ∀ f : G.Coloring (Fin 3), (∀ i j, f (c i) = f (c j) ↔ φ i = φ j) →
      ∃ f : G.Coloring (Fin 3), ∀ i, f (c i) = φ i := by
    intro f hf
    obtain ⟨π, hπ⟩ := exists_perm_of_pattern (fun i => f (c i)) φ hf
    exact ⟨recolour f π, hπ⟩
  rcases pattern_four φ hφ with ⟨h02, h13⟩ | ⟨r, h02, h13⟩
  · obtain ⟨f, f02, f13, f01⟩ : ∃ f : G.Coloring (Fin 3),
        f (c 0) = f (c 2) ∧ f (c 1) = f (c 3) ∧ f (c 0) ≠ f (c 1) :=
      exists_coloring_four_two hP h3 (hadj 0) (hadj 1) (hadj 2)
    have p01 : φ 0 ≠ φ 1 := hφ 0
    refine key f fun i j => ?_
    rcases zmod4_cases i 0 with h | h | h | h <;>
    rcases zmod4_cases j 0 with h' | h' | h' | h' <;>
    rw [h, h'] <;> simp only [zero_add] <;>
    simp [← f02, ← f13, ← h02, ← h13, f01, f01.symm, p01, p01.symm]
  · have e4 : r + 3 + 1 = r := by
      have : ∀ r : ZMod 4, r + 3 + 1 = r := by decide
      exact this r
    have hda : G.Adj (c (r + 3)) (c r) := by simpa [e4] using hadj (r + 3)
    have hbd : c (r + 1) ≠ c (r + 3) := fun h => by
      have := hinj h
      have : ∀ r : ZMod 4, r + 1 ≠ r + 3 := by decide
      exact this r ‹_›
    have hbc : G.Adj (c (r + 1)) (c (r + 2)) := by
      simpa [add_assoc, show (1 : ZMod 4) + 1 = 2 by decide] using hadj (r + 1)
    have hcd : G.Adj (c (r + 2)) (c (r + 3)) := by
      simpa [add_assoc, show (2 : ZMod 4) + 1 = 3 by decide] using hadj (r + 2)
    obtain ⟨f, f02, f13⟩ := exists_coloring_four_three hP h3 (hadj r) hbc hcd hda hbd
    have f01 := f.valid (hadj r)
    have f30 := f.valid hda
    have p01 := hφ r
    have p30 : φ (r + 3) ≠ φ r := by simpa [e4] using hφ (r + 3)
    refine key f fun i j => ?_
    rcases zmod4_cases i r with h | h | h | h <;>
    rcases zmod4_cases j r with h' | h' | h' | h' <;>
    rw [h, h'] <;>
    simp [← f02, ← h02, f01, f01.symm, f13, f13.symm, f30, f30.symm, p01, p01.symm, p30,
      p30.symm, h13, h13.symm]

/-- **Precolouring extension for 5-cycles.** In a triangle-free planar graph, every proper
3-colouring of a 5-cycle extends to the whole graph. -/
theorem exists_coloring_extend_five (hP : IsPlanar G) (h3 : G.CliqueFree 3) {c : ZMod 5 → V}
    (hadj : ∀ i, G.Adj (c i) (c (i + 1))) (φ : ZMod 5 → Fin 3)
    (hφ : ∀ i, φ i ≠ φ (i + 1)) : ∃ f : G.Coloring (Fin 3), ∀ i, f (c i) = φ i := by
  obtain ⟨r, h02, h13⟩ := pattern_five φ hφ
  have s1 : ∀ r : ZMod 5, r + 1 + 1 = r + 2 := by decide
  have s2 : ∀ r : ZMod 5, r + 2 + 1 = r + 3 := by decide
  have s3 : ∀ r : ZMod 5, r + 3 + 1 = r + 4 := by decide
  have s4 : ∀ r : ZMod 5, r + 4 + 1 = r := by decide
  have hbc : G.Adj (c (r + 1)) (c (r + 2)) := by simpa [s1] using hadj (r + 1)
  have hcd : G.Adj (c (r + 2)) (c (r + 3)) := by simpa [s2] using hadj (r + 2)
  have hde : G.Adj (c (r + 3)) (c (r + 4)) := by simpa [s3] using hadj (r + 3)
  have hea : G.Adj (c (r + 4)) (c r) := by simpa [s4] using hadj (r + 4)
  obtain ⟨f, f02, f13, f01, f40, f41⟩ :=
    exists_coloring_five hP h3 (hadj r) hbc hcd hde hea
  have p01 := hφ r
  have p34 : φ (r + 3) ≠ φ (r + 4) := by simpa [s3] using hφ (r + 3)
  have p40 : φ (r + 4) ≠ φ r := by simpa [s4] using hφ (r + 4)
  rw [← h13] at p34
  obtain ⟨π, hπ⟩ := exists_perm_of_pattern (fun i => f (c i)) φ fun i j => by
    rcases zmod5_cases i r with h | h | h | h | h <;>
    rcases zmod5_cases j r with h' | h' | h' | h' | h' <;>
    rw [h, h'] <;>
    simp [← f02, ← f13, ← h02, ← h13, f01, f01.symm, f40, f40.symm, f41, f41.symm, p01, p01.symm, p34, p34.symm, p40,
      p40.symm]
  exact ⟨recolour f π, hπ⟩

end Grotzsch
