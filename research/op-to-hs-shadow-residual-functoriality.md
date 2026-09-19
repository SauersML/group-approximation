---
rg: 2
id: op-to-hs-shadow-residual-functoriality
kind: claim
title: The operator-to-HS shadow residual is a functorial normal subgroup
distinct_from:
  mf-vs-tracial-radical-strict-gap: that claim proves the shadow residual can strictly exceed the MF residual; this claim establishes the subgroup and functoriality laws used by the compiler.
  hyperlinear-killed-normal-kazhdan-mf-transfer: that claim converts a killed normal Kazhdan subgroup into MF invisibility; this claim defines and transports the killed subgroup before any Kazhdan hypothesis is imposed.
artifacts:
  - research/artifacts/shadow-kleene-saturation-compiler-2026-08-22.md
  - GroupApproximation/Sofic/OpToHSShadowResidual.lean
---

For every group `G`, the elements killed in the normalized-HS ultraproduct
attached to every operator-norm almost representation form a normal subgroup

```text
S(G) = R_{infinity->2}(G).
```

For every homomorphism `f:G->H`,

```text
f(S(G)) <= S(H).
```

Thus embeddings preserve shadow bugs upward, quotients push them downward,
and `w in S(G)` implies `<<w>>^G <= S(G)`.  The input is genuinely weaker
than MF invisibility by `mf-vs-tracial-radical-strict-gap`.
