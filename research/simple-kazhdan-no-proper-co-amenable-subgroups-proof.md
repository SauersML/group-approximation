---
rg: 2
id: simple-kazhdan-no-proper-co-amenable-subgroups-proof
kind: route
title: No invariant mean on infinite coset spaces plus simplicity forces a co-amenable subgroup to be everything
target: simple-kazhdan-groups-have-no-proper-co-amenable-subgroups
requires:
  - no-invariant-mean-on-coset-space
artifacts:
  - research/artifacts/rokhlin-lower-bounds-without-finite-models-2026-09-12.md
---

Proposition 1.1 of the artifact.
1. By the prerequisite, a co-amenable `H` has finite index.
2. The permutation action on `G/H` has a normal kernel of finite index.
3. The kernel is not trivial, since `G` is infinite and does not embed in a finite symmetric group. By simplicity the kernel is `G`.
4. So every element fixes the coset `H`, and `H = G`.
