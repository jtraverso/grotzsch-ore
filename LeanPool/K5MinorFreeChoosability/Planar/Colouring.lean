/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.K5MinorFreeChoosability.Planar.Nonplanar
public import LeanPool.K5MinorFreeChoosability.Signed

/-!
# Five-colourings of planar graphs

The planar endpoints are derived from the `K_5`-minor-free theorems through the proved bridge
`cliqueMinorFree_five_of_isPlanar` (planar ⇒ no `K_5` minor).  No hypothesis other than
planarity (the existence of a genus-zero rotation system, `IsPlanar`) and finiteness is used.

* `exists_listColouring_of_isPlanar`, `choosableWith_five_of_isPlanar`: Thomassen (1994),
  every finite planar graph is 5-choosable, for finite lists over any colour type;
* `exists_dpColouring_of_isPlanar`, `dpColourableWith_five_of_isPlanar`: DP-5-colourability;
* `exists_signedListColouring_of_isPlanar`: signed 5-choosability.
-/

@[expose] public section

namespace LeanPool.K5MinorFreeChoosability

variable {V C : Type*}

/-- **Thomassen (1994)**: every finite planar graph has a proper colouring from any lists of
size at least five. -/
theorem exists_listColouring_of_isPlanar [Finite V] (G : SimpleGraph V) (hG : IsPlanar G)
    (L : V → Finset C) (hL : ∀ v, 5 ≤ (L v).card) : ListColourable G L :=
  exists_listColouring_of_k5MinorFree G (cliqueMinorFree_five_of_isPlanar hG) L hL

/-- **Thomassen (1994)**, choosability form. -/
theorem choosableWith_five_of_isPlanar [Finite V] (G : SimpleGraph V) (hG : IsPlanar G)
    (C : Type*) : ChoosableWith G C 5 :=
  choosableWith_five_of_k5MinorFree G (cliqueMinorFree_five_of_isPlanar hG) C

/-- Finite planar graphs are DP-5-colourable: every correspondence on lists of size at least
five admits a colouring. -/
theorem exists_dpColouring_of_isPlanar [Finite V] (G : SimpleGraph V) (hG : IsPlanar G)
    (L : V → Finset C) (M : V → V → C → C → Prop) (hM : IsCorrespondence M)
    (hL : ∀ v, 5 ≤ (L v).card) : DPColourable G L M :=
  exists_dpColouring_of_k5MinorFree G (cliqueMinorFree_five_of_isPlanar hG) L M hM hL

theorem dpColourableWith_five_of_isPlanar [Finite V] (G : SimpleGraph V) (hG : IsPlanar G)
    (C : Type*) : DPColourableWith G C 5 :=
  dpColourableWith_five_of_k5MinorFree G (cliqueMinorFree_five_of_isPlanar hG) C

/-- Signed 5-choosability of finite planar graphs. -/
theorem exists_signedListColouring_of_isPlanar [Finite V] (G : SimpleGraph V)
    (hG : IsPlanar G) (σ : V → V → ℤˣ) (hσ : ∀ u v, G.Adj u v → σ u v = σ v u)
    (L : V → Finset ℤ) (hL : ∀ v, 5 ≤ (L v).card) :
    ∃ c : V → ℤ, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ (σ u v : ℤ) * c v :=
  exists_signedListColouring_of_k5MinorFree G (cliqueMinorFree_five_of_isPlanar hG) σ hσ L hL

end LeanPool.K5MinorFreeChoosability
