/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Extension

/-!
# Signed list colourings of `K_5`-minor-free graphs

A signature on `G` is a map `σ : V → V → ℤˣ` with `σ u v = σ v u` on every edge `uv`.
A signed list colouring from integer lists `L` is a choice `c v ∈ L v` with
`c u ≠ σ u v * c v` for every edge `uv`.

We prove that the forbidden relation `x = σ u v * y` (restricted to edges) is a
correspondence (a symmetric family of partial matchings), and deduce from the DP form of
Wood--Linusson's Lemma 7 that finite `K_5`-minor-free signed graphs are signed
5-choosable.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V : Type*}

/-- The forbidden relation of a signed graph: on an edge `uv`, colour `x` at `u` conflicts
with colour `y` at `v` iff `x = σ u v * y`. -/
def signedCorrespondence (G : SimpleGraph V) (σ : V → V → ℤˣ) : V → V → ℤ → ℤ → Prop :=
  fun u v x y => G.Adj u v ∧ x = (σ u v : ℤ) * y

/-- The signed forbidden relation is a correspondence (a matching on each edge). -/
theorem isCorrespondence_signedCorrespondence (G : SimpleGraph V) (σ : V → V → ℤˣ)
    (hσ : ∀ u v, G.Adj u v → σ u v = σ v u) :
    IsCorrespondence (signedCorrespondence G σ) where
  symm u v x y h := by
    obtain ⟨hadj, rfl⟩ := h
    refine ⟨hadj.symm, ?_⟩
    rw [← hσ u v hadj]
    rcases Int.units_eq_one_or (σ u v) with hs | hs <;> simp [hs]
  unique u v x y y' h h' := by
    obtain ⟨_, rfl⟩ := h
    obtain ⟨_, h'⟩ := h'
    rcases Int.units_eq_one_or (σ u v) with hs | hs <;> simpa [hs] using h'

/-- **Signed 5-choosability of `K_5`-minor-free graphs.** For every finite
`K_5`-minor-free graph `G`, every signature `σ` (symmetric on edges) and every assignment of
integer lists of size at least five, there is a colouring `c` from the lists with
`c u ≠ σ u v * c v` for every edge `uv`. -/
theorem exists_signedListColouring_of_k5MinorFree [Finite V] (G : SimpleGraph V)
    (hG : CliqueMinorFree G 5) (σ : V → V → ℤˣ) (hσ : ∀ u v, G.Adj u v → σ u v = σ v u)
    (L : V → Finset ℤ) (hL : ∀ v, 5 ≤ (L v).card) :
    ∃ c : V → ℤ, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ (σ u v : ℤ) * c v := by
  obtain ⟨c, hcL, hc⟩ := exists_dpColouring_of_k5MinorFree G hG L
    (signedCorrespondence G σ) (isCorrespondence_signedCorrespondence G σ hσ) hL
  exact ⟨c, hcL, fun u v huv h => hc u v huv ⟨huv, h⟩⟩

end LeanPool.K5MinorFreeChoosability
