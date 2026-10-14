# Grötzsch's theorem, Ore's conjecture for k = 4 and the Grünbaum–Aksenov theorem in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

This repository formalizes, for finite simple graphs in Lean 4 with Mathlib:

1. **Kostochka–Yancey (2014), Ore's conjecture for `k = 4`.** Every 4-critical graph `G` (not
   3-colourable, but every vertex- or edge-deleted subgraph is) satisfies
   `3 |E(G)| ≥ 5 |V(G)| - 2`.
2. **Grötzsch's theorem (1959).** Every finite triangle-free planar graph is 3-colourable.
3. **Aksenov (1974); Jensen–Thomassen (2000).** A triangle-free planar graph plus one edge is
   3-colourable.
4. **Borodin–Kostochka–Lidický–Yancey (2014), Theorem 4.** A triangle-free planar graph plus one
   vertex of degree at most 4 is 3-colourable.
5. **Grünbaum (1963); Aksenov (1974).** Every finite planar graph with at most three triangles is
   3-colourable.

The audited statements are in [`Challenge.lean`](Challenge.lean), which imports only Mathlib and
contains the definition of planarity; the proofs are in [`Solution.lean`](Solution.lean).
[`comparator.json`](comparator.json) lists the compared theorems and
[`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md) reproduces verbatim the Mathlib definitions
used by the statements (at the pinned Mathlib revision), and
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
* **BKLY Theorems 4 and 2** (`Grotzsch/PlusVertex.lean`, `Grotzsch/PlusEdge.lean`), following
  Borodin–Kostochka–Lidický–Yancey: a smallest counterexample is 4-critical; Euler's formula with
  at most one exceptional face contradicts Kostochka–Yancey, and otherwise identifying opposite
  corners of a 4-face gives a smaller graph of the same kind; the crossing claims are again
  `K₅`-minor arguments with an apex inside a face.
* **Precolouring extension** (`Grotzsch/CycleExtension.lean`): in a triangle-free planar graph
  every proper 3-colouring of any 4- or 5-cycle extends (BKLY Theorem 5, for any cycle, not only
  faces): the pattern of the colouring is forced by an extra vertex of degree 4 or an extra chord,
  using Theorems 4 and 2.
* **Regions of a subgraph** (`Grotzsch/Regions.lean`, `Grotzsch/FacialCycle.lean`): a
  combinatorial Jordan-type theorem for rotation systems. The rotation induced on a subgraph `H`
  is again a plane map; all darts leading into one component of `G - V(H)`, and both ends of a
  chord, lie in one face of `H`; a face of `H` that is a face of `G` is empty. In particular a
  chordless cycle whose complement is connected is a face.
* **Grünbaum–Aksenov** (`Grotzsch/GrunbaumAksenov.lean`, `Grotzsch/GACases.lean`,
  `Grotzsch/GACase3.lean`), following BKLY Theorem 7: a smallest counterexample is 4-critical,
  cliques do not separate it (so triangles are faces), both sides of a separating 4- or 5-cycle
  contain triangles (precolouring extension), and some face has length 4 (Euler with at most
  three triangular faces). Case 2 (a chord of a 4-face) forces a vertex of degree 2; Lemma 10
  (identification of opposite corners plus crossing) gives a triangle next to the face, and the
  two configurations of Case 3 are eliminated with identifications, 4-critical subgraphs,
  `K₅`-minor arguments and, for Case 3.2, the region theorem, which makes the "interiors" and
  the "outer face" of the paper precise.

`LeanPool/K5MinorFreeChoosability/` contains 22 modules of the author's own planarity library
(plane maps, Euler's formula, face lengths, minor-closedness, `K₅`/`K₃,₃` non-planarity, apex
extension), included verbatim.

## Scope and limitations

* Planarity is combinatorial (see above).
* The Kostochka–Yancey bound, BKLY Theorems 2 and 4 and the Grünbaum–Aksenov theorem are stated
  for vertex types in `Type`; Grötzsch's theorem for any universe.
* No `sorry`, no custom axioms; the compared theorems depend only on `propext`,
  `Classical.choice` and `Quot.sound`.

## Sources

* A. Kostochka, M. Yancey, *Ore's conjecture for k = 4 and Grötzsch's theorem*, Combinatorica 34
  (2014) 323–329, arXiv:1209.1173.
* O. V. Borodin, A. V. Kostochka, B. Lidický, M. Yancey, *Short proofs of coloring theorems on
  planar graphs*, European J. Combin. 36 (2014) 314–321, arXiv:1211.3981.
* H. Grötzsch, *Zur Theorie der diskreten Gebilde VII: Ein Dreifarbensatz für dreikreisfreie
  Netze auf der Kugel*, Wiss. Z. Martin-Luther-Univ. Halle-Wittenberg 8 (1958/59) 109–120.
* B. Grünbaum, *Grötzsch's theorem on 3-colorings*, Michigan Math. J. 10 (1963) 303–310.
* V. A. Aksenov, *On continuation of 3-colouring of planar graphs* (Russian), Diskret. Analiz 26
  (1974) 3–19.
* O. V. Borodin, *A new proof of Grünbaum's 3 color theorem*, Discrete Math. 169 (1997) 177–183.
* T. R. Jensen, C. Thomassen, *The color space of a graph*, J. Graph Theory 34 (2000) 234–245.
* O. Ore, *The Four Color Problem*, Academic Press, 1967 (background).
* J. Edmonds, *A combinatorial representation for polyhedral surfaces*, Notices AMS 7 (1960) 646
  (background on rotation systems).

We are not aware of a prior formalization of these theorems; this was checked against Mathlib,
the Lean Pool collection and the Palomar registry, not by an exhaustive literature search.

## Authorship and use of AI

The choice of results, proof routes and statements, and the planarity library, are by the
author. The Lean code of this repository was written with an AI agent (Claude Opus 5.5 in Claude
Code); several proofs (the Kostochka–Yancey claims in `Grotzsch/Ore.lean`, BKLY Theorems 2 and 4,
the facial-cycle and region theorems, Cases 2 and 3 of Grünbaum–Aksenov) were produced by
Harmonic's Aristotle from formal statements and proof plans, and audited. Some intermediate claims
were first tested numerically with the `certo` toolkit. Every result was checked mechanically with
Lean. See `formalization.yaml` for details.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```

Submissions to the Palomar registry go through https://submit.palomar-registry.org/.
