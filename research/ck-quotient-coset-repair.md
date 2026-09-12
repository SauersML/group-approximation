---
rg: 2
id: ck-quotient-coset-repair
kind: claim
title: A nontrivial finitely presented quotient repairs the canonical CK core coset action
refuted_by: [ck-quotient-corner-has-infinite-bi-index]
distinct_from:
  ck-envelope-simple-core-has-finite-bi-index: that permits other envelopes and embeddings; this restricts the repair to a quotient of the direct elementary envelope with its inherited corner core.
artifacts:
  - research/artifacts/ck-quotient-and-cover-bi-index-obstruction-2026-09-08.md
---

For each infinite finitely generated computably presented simple core `S`,
choose its direct universal-sandwich envelope `Gamma=EL_4(U)` with corner
subgroup `D`. There exists a proper normal subgroup `N` with `Gamma/N`
finitely presented and the inherited subgroup `q(D)` of finite bi-index.

This is false: `ck-quotient-corner-has-infinite-bi-index` gives infinitely
many double cosets for every proper `N`, without needing any finiteness
assumption on `Gamma/N`.

## Attempts

The August 31 audit suggested collapsing spare roots in a controlled
quotient while preserving the core. Individual roots can collapse, but
their surviving parameter group is `U/lev(N)`, which stays infinite.
This rules out the proposed repair, including choices with finitely
normally generated kernels. A simple finitely presented quotient would
still solve Boone–Higman directly, without making the core bi-index finite.
