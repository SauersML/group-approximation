---
rg: 2
id: some-f-infinity-finite-cd-group-has-no-contractible-rips
kind: claim
title: Some group of type F_infinity with finite cohomological dimension has no contractible Rips complex
distinct_from:
  f-infinity-finite-cd-groups-have-contractible-rips: that is the affirmative answer to Problem 4.6; this is its negation, the negative answer
  some-type-f-group-has-no-contractible-rips-complex: that is the negative answer to Problem 4.7, a type F witness; this is the negative answer to Problem 4.6, whose witness may also be a group that is not of type F
  some-f-infinity-group-of-finite-cd-is-not-of-type-f: that is the negative answer to Problem 1.21, about finite classifying spaces; this is about Rips complexes, and that claim implies this one
---

There is a group `G` of type `F_∞` with `cd G < ∞` such that for every finite
symmetric generating set `S` and every scale `r ≥ 1` the closed Rips complex
`R_r(G,S)` is not contractible.

The negative answer to Zaremsky Problem 4.6
(`zaremsky-4-06-f-infinity-finite-cd-contractible-rips`); the negation of
`f-infinity-finite-cd-groups-have-contractible-rips`.

## Attempts

- **Through Problem 1.21, wired.** `no-contractible-rips-from-f-infinity-group-not-of-type-f`
  requires `some-f-infinity-group-of-finite-cd-is-not-of-type-f` and
  `contractible-rips-complex-gives-finite-classifying-space`. Where it stops: such
  a `G` has `σ(G) ≠ 0` and `K̃_0(ZG) ≠ 0`
  (`fp-type-fp-group-is-type-f-iff-wall-class-vanishes`,
  `f-infinity-finite-cd-group-with-zero-reduced-k0-is-type-f`), so it refutes
  Lück–Reich Conjecture 1.3 for torsion-free groups. None is known. In every Rips
  complex of `G` acyclic below its top dimension, `σ(G)` is the class of the top
  homology (`top-homology-of-free-complex-carries-wall-obstruction`).
- **Through Problem 4.7, wired.** `no-contractible-rips-from-type-f-group-without-one`
  requires `some-type-f-group-has-no-contractible-rips-complex`. Where it stops:
  an obstruction must hold for every finite generating set and every scale.
  Rescaling (`R_r(G,S) = R_1(G, B_S(r) ∖ {1})`,
  `rips-complex-of-a-group-is-a-flag-cayley-complex`) shows this means `G`
  admits no simplicial action on a locally finite contractible flag complex that is
  simply transitive on vertices. The Euler characteristic does not obstruct: with
  `c_k` the number of `k`-simplices of `R_1(G,S)` containing the identity,
  `χ(G) = Σ_k (−1)^k c_k/(k+1)` holds automatically and imposes only integrality.
  No invariant is known that separates all Cayley flag complexes of a type F group
  from contractible ones.
- **The two witnesses meet.** If `G` answers Problem 1.21 negatively, the type F
  group `G × Z` has no contractible Rips complex for any product generating set
  (`counterexample-times-z-lacks-contractible-product-rips`). So it is a
  candidate for this claim through Problem 4.7, but other generating sets of
  `G × Z` are not controlled.
