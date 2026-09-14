---
rg: 2
id: fp-groups-without-free-subgroups-split-ascendingly-over-kernels
kind: claim
title: A finitely presented group with no non-abelian free subgroup splits ascendingly over a finitely generated subgroup of the kernel of any map onto Z
distinct_from:
  bieri-strebel-splitting-over-kernel-of-map-to-z: that imports the general splitting HNN(H,K,L,phi) with no ascending conclusion; this imports the corollary that without a non-abelian free subgroup the splitting can be taken ascending, which gives a one-sided exhaustion of the kernel.
  fp-bvc-group-mapping-onto-z-is-ascending-hnn-extension: that derives an ascending splitting from property BVC; this derives it from the absence of non-abelian free subgroups, for example for every solvable group.
artifacts:
  - research/artifacts/hl-bh-universal-2-2026-09-13.md
---

**ESTABLISHED** as a citation import (`fp-groups-without-free-subgroups-ascending-splitting-citation`).

## Statement

Let `G` be a finitely presented group containing no free subgroup of rank 2, and let
`pi: G -> Z` be surjective. Then for `eps = 1` or `eps = -1` there are a finitely generated
subgroup `H <= ker(pi)` and an element `s` with `pi(s) = eps` such that

    ker(pi) = union_(n >= 0) s^-n H s^n,   H <= s^-1 H s,

or the same with `s` replaced by `s^-1` and `H <= s H s^-1`. That is, the kernel is an
increasing union of conjugates of `H` by powers of a single element of degree `+-1`.

In particular this applies to every finitely presented solvable group, since solvable
groups contain no free subgroup of rank 2.

DERIVATION
fp-groups-without-free-subgroups-ascending-splitting-citation
