---
rg: 2
id: some-infinite-planar-set-has-a-non-wedge-rips-complex
kind: claim
title: "Some infinite planar set has a connected Rips complex that is not homotopy equivalent to a wedge of spheres"
distinct_from:
  rips-complexes-of-planar-sets-are-wedges-of-spheres: that claim is the universal positive statement over all subsets; this claim asks for one infinite counterexample
---

There are an infinite set `X ⊆ R^2` (Euclidean metric) and a scale `r > 0`
such that `R_r(X)` (with the closed or the strict diameter convention) is
connected and not homotopy equivalent to any wedge of spheres.

`some-finite-planar-set-has-a-non-wedge-rips-complex` implies this claim (add
infinitely many near-twins of one point; see that claim). This claim matters
separately only if the finite reading has a positive answer.

## Attempts

- Infinite sets allow critical scales where the closed and strict conventions
  differ, and complexes of infinite dimension. For the circle at its critical
  scales, Adamaszek–Adams report wedges of uncountably many even spheres
  (context, unverified here), which is still a wedge.
- No infinite-specific mechanism is recorded yet; the periodic-strip attack
  (C) on the finite negation produces finite sets.
- 2026-09-18 (swarm-0917-w10-w10-z-break): fundamental-group certificates are
  dead for countable sets. By
  `planar-rips-pi1-is-aleph1-free-and-free-when-countable`, `π_1(R_r(X))` is
  free for every countable `X ⊆ R^2`, and `ℵ_1`-free for every `X`.
  - The proof goes through the new planar lemma
    `planar-polyhedron-inclusions-have-free-factor-pi1-images`. That lemma
    closes the gap recorded in §6 of
    `research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md`.
  - Together with free `H_1` (`planar-rips-complexes-have-free-first-homology`),
    a countable counterexample must be certified in degree `≥ 2`: by `π_{≥2}`,
    `H_{≥2}`, the `π_1`-action on higher homotopy, or `k`-invariants.
  - A non-free `π_1` remains a possible certificate only for uncountable `X`.
    There it would have to be a non-free `ℵ_1`-free group. The precise missing
    coherence statement is recorded in the Attempts of the `π_1` claim.
  - This claim stays open.
