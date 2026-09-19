---
rg: 2
id: stw22-diffuse-weighted-purification-uniform-loop-fillings
kind: claim
title: Weighted purification fibres in every separable II1 factor are uniformly one-connected
distinct_from:
  stw22-weighted-equi-lc1-reduces-to-unweighted-stiefel-filling: that theorem is the hyperfinite-factor case; the present theorem removes hyperfiniteness by combining diffuse spectral capture with a relative moving-complement extension.
  stw22-diffuse-stiefel-uniform-loop-fillings: that theorem treats projection weights only; the present theorem permits arbitrary positive weights with spectrum accumulating at zero.
artifacts:
  - research/artifacts/stw22-dim2-arbitrary-factor-breakthrough-2026-08-30.md
---

Let `(N,tau)` be a II1 factor with separable predual, let `e in N` be a
projection, and fix `s<tau(e)`. For

```text
F_e(a)={w in eN:w^*w=a},
0<=a<=1,       tau(supp(a))<=s,                         (DW1)
```

the family of all `F_e(a)`, inside the complete operator-norm unit ball
of `L^2(N)`, is uniformly equi-`LC^1`. Explicitly, for every
`epsilon>0` there is one `rho(epsilon)>0`, independent of `a`, such
that every loop in one `F_e(a)` lying in a `rho(epsilon)`-ball fills
inside the concentric `epsilon`-ball.

Every individual `F_e(a)` is path connected and simply connected.
The set-valued map `a |-> F_e(a)` is lower semicontinuous in the
`2`-norm. Hence every `2`-norm-continuous field of positive contractions

```text
a:X->N_+,       tau(supp(a(x)))<=s,
```

over a compact Hausdorff space of covering dimension at most two admits a
`2`-norm-continuous weighted purification `w:X->eN` with `w^*w=a`.

The trace gap `tau(e)-s>0` is essential to the uniform family statement.
No hyperfiniteness, property Gamma, spectral gap, or continuous support
projection is assumed.
