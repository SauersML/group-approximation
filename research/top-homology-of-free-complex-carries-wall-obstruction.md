---
rg: 2
id: top-homology-of-free-complex-carries-wall-obstruction
kind: claim
title: A free cocompact complex acyclic below its top dimension carries the Wall finiteness obstruction in its top homology
distinct_from:
  contractible-rips-complex-gives-finite-classifying-space: that says a contractible Rips complex of a torsion-free group gives a finite K(G,1); this locates the finiteness obstruction of a type FP group in the top homology of any free cocompact complex that is acyclic below its dimension, for instance a Rips complex
  fp-type-fp-group-is-type-f-iff-wall-class-vanishes: that is the criterion type F iff sigma(G) = 0 for finitely presented FP groups; this computes sigma(G) as the class of the top homology of a free cocompact complex acyclic below its dimension
---

Let `G` be a group of type FP with `cd G = d`, and let
`σ(G) ∈ K̃_0(ZG)` be its finiteness obstruction: the class
`Σ_i (−1)^i [P_i]` of any finite projective resolution `P_*` of `Z`. It is
well defined by Schanuel's lemma, and `σ(G) = 0` iff `G` is of type FF. Let `X`
be a connected free cocompact `G`-CW complex of dimension `N ≥ d` with
`H_k(X; Z) = 0` for `1 ≤ k ≤ N − 1`. Then `H_N(X; Z)` is a finitely generated
projective `ZG`-module and

`σ(G) = (−1)^{N+1} [H_N(X)]` in `K̃_0(ZG)`.

Consequences for a torsion-free `G` of type FP and a Rips complex
`X = R_r(G,S)` of dimension `N ≥ d` that is acyclic below dimension `N`:

- if `σ(G) ≠ 0`, then `H_N(X)` is not stably free, in particular nonzero. The
  whole finiteness obstruction sits in the top homology, and lower-degree
  acyclicity is no evidence for contractibility;
- if `G` is finitely presented and `H_N(X)` is stably free, then `σ(G) = 0`, so
  `G` is of type F by `fp-type-fp-group-is-type-f-iff-wall-class-vanishes`.

For Zaremsky Problems 4.6 and 1.21: a Rips-complex proof that every group of
type `F_∞` with finite cd is of type F must kill the top homology of some level
that is already acyclic below the top, or reach a stably free top homology. A
counterexample to Problem 1.21 is detected exactly by a non-stably-free top
homology module.

Credit: this is Wall's finiteness-obstruction bookkeeping (C. T. C. Wall,
*Finiteness conditions for CW-complexes*, Ann. of Math. 81 (1965); K. S. Brown,
*Cohomology of Groups*, Ch. VIII). Only the Rips-complex reading is new here.

Proof: `top-homology-of-free-complex-carries-wall-obstruction-proof`.
