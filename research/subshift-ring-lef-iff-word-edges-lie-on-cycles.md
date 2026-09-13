---
rg: 2
id: subshift-ring-lef-iff-word-edges-lie-on-cycles
kind: claim
title: A finite-field subshift ring is LEF exactly when it is directly finite and every word edge lies on a cycle
distinct_from:
  minimal-subshift-algebra-is-simple-lef-ring: that assumes minimality and proves simplicity and LEF; this characterizes direct finiteness, stable finiteness and LEF for every nonempty finite-alphabet subshift.
  strong-word-graphs-give-short-primitive-periodic-models: that treats one strongly connected graph and a single primitive orbit; this permits multiple components and retains enlarged periods in finite products of ring models.
artifacts:
  - research/artifacts/pestov91-subshift-lef-mf-dichotomy-2026-09-13.md
---

Let `X` be any nonempty finite-alphabet subshift and `F_q` any finite
field. For `R_X=LC(X,F_q) semidirect Z`, the following are equivalent:

- every edge in every directed prefix-suffix word graph lies on a cycle;
- there is no clopen `U` with `T(U)` a proper subset of `U`;
- `R_X` is directly finite;
- `R_X` is stably finite;
- `R_X` is LEF as a unital ring.

If a word edge fails the cycle test, the set of vertices reachable from
its terminal vertex gives a clopen `U` with strict forward inclusion.
Writing `p=1_U`, the explicit pair `s=up+1-p`, `t=pu^{-1}+1-p` satisfies
`ts=1` and `1-st=1_(U minus T(U))!=0`.
