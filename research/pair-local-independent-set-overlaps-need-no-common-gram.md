---
rg: 2
id: pair-local-independent-set-overlaps-need-no-common-gram
kind: claim
title: Independent-set overlap rows can be wordized with pair-local sources
artifacts:
  - research/artifacts/independent-set-rounding-rank-router-2026-08-23.md
distinct_from:
  fixed-mass-same-gram-mixed-word-certificate: that must transport every BCS predicate and consistency row on one fixed positive Gram; this starts after independent-set normalization and lets each forbidden pair use its own row projection.
  rank-conjugacy-detects-projection-overlap: that is the stronger source-free two-copy detector; this records the already available partial-isometry fallback.
---

**ESTABLISHED.**  Let `(P_i^u)` be one finite row-PVM strategy for an
independent-set game.  For each forbidden pair `f=((i,u),(j,v))`, the
projection `S_f=P_j^v`, together with

```text
A_f=1-2P_i^u,            B_f=1,
```

is a pair-local partial-isometry source.  The ordinary swap word from
`partial-isometry-swap-wordizes-one-bcs-gram-row` satisfies

```text
4||P_i^uP_j^v||_2^2
 <=||C_f-1||_2^2
 <=20||P_i^uP_j^v||_2^2.                              (PLO1)
```

Different forbidden pairs may use different `S_f`: the single global game
state is already the row-PVM family itself.  Hence independent-set
normalization removes the analytic common-Gram requirement even before the
stronger rank-conjugacy detector is used.

