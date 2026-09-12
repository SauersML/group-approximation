---
rg: 2
id: mci-exact-endpoint-is-fd-radical
kind: claim
title: Exact cyclic-carrier invariance is finite-dimensional group-algebra radical membership
artifacts:
  - research/artifacts/cyclic-carrier-energy-and-outlier-audit-2026-08-21.md
distinct_from:
  matrix-only-cyclic-carrier-invariance: that asks for a dimension-uniform modulus on approximate representations; this identifies only its exact zero-defect endpoint and proves why the missing uniformity is substantive.
  matricial-stability-identifies-radicals: that compares group-element MF and finite-dimensional residuals under full matricial stability; this concerns additive commutators in the group algebra and assumes no stability.
---

For `G=<X|R>`, a finite set `S subset G`, a word `w`, and a trigonometric
polynomial `f`, put

```text
p_s=[s,f(w)] in C[G].
```

If `matrix-only-cyclic-carrier-invariance` holds, then

```text
p_s in intersection_(d,pi:G->U(d)) ker(pi)
```

for every `s in S`. Conversely this radical membership is exactly the
zero-defect endpoint of the desired estimate. If canonical no-capture gives
positive regular energy, some `p_s` is nonzero, so `C*(G)` is not RFD and
`G` cannot be residually finite.

The last implication is direct: a finite quotient injective on the finite
support of a nonzero group-algebra element sends it to a nonzero element of a
finite group algebra, which its regular representation detects.

For each fixed dimension, compactness of `U(d)^X` promotes the exact endpoint
to a dimension-dependent modulus. The unsolved statement is precisely the
uniform interchange of limits over defect and dimension.
