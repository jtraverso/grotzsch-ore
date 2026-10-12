# Grötzsch's theorem and Ore's conjecture for k = 4 in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

This repository formalizes, for finite simple graphs in Lean 4 with Mathlib:

1. **Kostochka–Yancey (2014), Ore's conjecture for `k = 4`.** Every 4-critical graph `G` (not
   3-colourable, but every vertex- or edge-deleted subgraph is) satisfies
   `3 |E(G)| ≥ 5 |V(G)| - 2`.
2. **Grötzsch's theorem (1959).** Every finite triangle-free planar graph is 3-colourable.

The audited statements are in [`Challenge.lean`](Challenge.lean), which imports only Mathlib and
contains the definition of planarity; the proofs are in [`Solution.lean`](Solution.lean).
[`comparator.json`](comparator.json) lists the compared theorems and
[`formalization.yaml`](formalization.yaml) records provenance, sources and process.

## Planarity

Mathlib has no planar graphs, so planarity is defined combinatorially: `G` is planar if it has a
*plane map*, a rotation system (a cyclic order of the darts at every vertex) whose hypermap has
Euler defect `|D| + 2K - c(rot) - c(dartSymm) - c(rot ∘ dartSymm) = 0`, i.e. every component has
genus `0`. This is the classical combinatorial description of sphere embeddings
(Heffter–Edmonds–Ringel); the equivalence with topological embeddings is not formalized. As sanity
checks, the Challenge states that `K₄` is planar and `K₅`, `K₃,₃` are not.

## How the proofs go

* **Kostochka–Yancey** (`Grotzsch/Ore.lean`). A vertex-minimal counterexample `G` is 4-critical
  with potential `ρ(V) = 5|V| - 3|E| > 2`, and every smaller non-3-colourable graph contains a
  vertex set of potential `≤ 2` spanning a non-3-colourable subgraph. Claims 9–10 (via the
  auxiliary graph `Y(G, R, φ)`) show that proper subsets have potential `≥ 6`, with equality only
  for triangles; Claims 11–13 exclude `K₄ - e`, triangles with two vertices of degree 3, and
  adjacent degree-3 vertices outside triangles; a discharging argument then gives `3|E| ≥ 5|V|`.
* **Grötzsch** (`Grotzsch/Planar.lean`). A counterexample with fewest vertices plus edges is
  4-critical. If every face has length `≥ 5`, Euler's formula gives `3|E| ≤ 5|V| - 10`,
  contradicting the bound. Otherwise there is a face `x y z u` with four distinct vertices.
  Identifying `x` and `z` gives a smaller planar graph (a minor of `G` plus an apex inside the
  face), so it must contain a triangle, i.e. a path `x b c z`; likewise a path `y b' c' u`.
  Triangle-freeness forces all eight vertices to be distinct, and then the apex and the two paths
  form a `K₅` minor of a planar graph — impossible. This replaces the topological crossing
  argument of the paper.

`LeanPool/K5MinorFreeChoosability/` contains 22 modules of the author's own planarity library
(plane maps, Euler's formula, face lengths, minor-closedness, `K₅`/`K₃,₃` non-planarity, apex
extension), included verbatim.

## Scope and limitations

* Planarity is combinatorial (see above).
* The Kostochka–Yancey bound is stated for vertex types in `Type`; Grötzsch's theorem for any
  universe.
* No `sorry`, no custom axioms; the compared theorems depend only on `propext`,
  `Classical.choice` and `Quot.sound`.

## Sources

* A. Kostochka, M. Yancey, *Ore's conjecture for k = 4 and Grötzsch's theorem*, Combinatorica 34
  (2014) 323–329, arXiv:1209.1173.
* H. Grötzsch, *Zur Theorie der diskreten Gebilde VII: Ein Dreifarbensatz für dreikreisfreie
  Netze auf der Kugel*, Wiss. Z. Martin-Luther-Univ. Halle-Wittenberg 8 (1958/59) 109–120.
* O. Ore, *The Four Color Problem*, Academic Press, 1967 (background).
* J. Edmonds, *A combinatorial representation for polyhedral surfaces*, Notices AMS 7 (1960) 646
  (background on rotation systems).

We are not aware of a prior formalization of Grötzsch's theorem or of the Kostochka–Yancey bound;
this was checked against Mathlib, the Lean Pool collection and the Palomar registry, not by an
exhaustive literature search.

## Authorship and use of AI

The choice of results, proof route and statements, and the planarity library, are by the author.
The Lean code of this repository was written with an AI agent (Claude Opus 5.5 in Claude Code);
the proofs of the Kostochka–Yancey claims in `Grotzsch/Ore.lean` were produced by Harmonic's
Aristotle from formal statements and proof sketches, and audited. Every result was checked
mechanically with Lean. See `formalization.yaml` for details.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```

Submissions to the Palomar registry go through https://submit.palomar-registry.org/.
