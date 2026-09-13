---
rg: 2
id: some-f-infinity-finite-cd-group-has-no-contractible-rips
kind: claim
title: Some group of type F_infinity with finite cohomological dimension has no contractible Rips complex
distinct_from:
  f-infinity-finite-cd-groups-have-contractible-rips: that is the affirmative answer to Problem 4.6; this is its negation, the negative answer
---

There is a group `G` of type `F_∞` with `cd G < ∞` such that for every finite
symmetric generating set `S` and every scale `r ≥ 1` the closed Rips complex
`R_r(G,S)` is not contractible.

The negative answer to Zaremsky Problem 4.6
(`zaremsky-4-06-f-infinity-finite-cd-contractible-rips`); the negation of
`f-infinity-finite-cd-groups-have-contractible-rips`.

## Attempts

- **Through Problem 1.21.** A group of type `F_∞` with finite cd that is not
  of type F has no contractible Rips complex, by
  `contractible-rips-complex-gives-finite-classifying-space`. Such a group is
  finitely presented of type FP with nonzero Wall finiteness obstruction
  `σ(G) ∈ K̃_0(ZG)`. Where it stops: for torsion-free `G` the K-theoretic
  Farrell–Jones conjecture predicts `K̃_0(ZG) = 0`, so a counterexample must be a
  finitely presented torsion-free group violating that conjecture in degree 0.
  None is known. The Problem 1.21 lanes own this search.
- **Through Problem 4.7.** A type F group with no contractible Rips complex
  answers 4.6 negatively, since type F implies `F_∞` and finite cd. Where it
  stops: an obstruction must hold for every finite generating set and every
  scale. Rescaling the generating set (`R_r(G,S) = R_1(G, B_S(r) ∖ {1})`)
  shows this is the same as: `G` admits no simplicial action on a locally finite
  contractible flag complex that is simply transitive on vertices. The Euler characteristic does not
  obstruct: with `c_k` the number of `k`-simplices of `R_1(G,S)` containing the
  identity, `χ(G) = Σ_k (−1)^k c_k/(k+1)` holds automatically and imposes only
  integrality. No invariant is known that separates all Cayley flag complexes of
  a type F group from contractible ones.
