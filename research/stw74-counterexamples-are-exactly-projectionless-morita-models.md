---
rg: 2
id: stw74-counterexamples-are-exactly-projectionless-morita-models
kind: claim
title: LXXIV counterexamples are exactly projectionless Morita models with infinite projective stabilization
distinct_from:
  stw74-counterexamples-are-unstably-projectionless: that extracts necessary data from a counterexample; this theorem proves the converse and hence gives an exact normal form.
artifacts:
  - research/artifacts/stw74-property-sp-cu-stability-audit-2026-08-30.md
---

A counterexample to Problem LXXIV exists if and only if there is a nonzero
sigma-unital simple C-star algebra `D` such that

```text
D has no nonzero projections,
D is not purely infinite,
D tensor K contains a nonzero projection,
every nonzero projection in D tensor K is properly infinite.       (NF)
```

If a separable counterexample is sought, `D` may and must be taken
separable.  Given `(NF)`, every nonzero projection `p in D tensor K` yields
a counterexample

```text
A_p = p(D tensor K)p.
```

Conversely every counterexample is Morita equivalent to such a `D`.

Thus the universal problem is exactly the existence problem for a
projectionless but not stably projectionless simple Morita model whose
entire stabilized projection semigroup is already properly infinite.
