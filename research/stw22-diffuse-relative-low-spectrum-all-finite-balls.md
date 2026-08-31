---
rg: 2
id: stw22-diffuse-relative-low-spectrum-all-finite-balls
kind: claim
title: Diffuse low-spectrum boundary data extend relatively in every finite ball dimension
distinct_from:
  stw22-diffuse-relative-low-spectrum-five-ball-extension: that theorem expands the four-sphere case; the present theorem proves the same recursion for every finite boundary degree.
artifacts:
  - research/artifacts/stw22-diffuse-all-degree-induction-audit-2026-08-31.md
---

For every finite `d>=0`, let `H:B^(d+1)->eN` be a continuous fixed-source
frame in a separable-predual II1 factor, put `f=e-HH^*`, and let `b` have
support `p_l` with

```text
tau(H^*H)+tau(p_l)<tau(e).                            (AD-2)
```

Every boundary map `x:S^d->eN` with `x^*x=b` and `fx=x` extends over
`B^(d+1)` with the same equations. If `b<=eta`, the extension has distance
at most `2sqrt(tau(b))<=2sqrt(eta tau(p_l))` from any fixed point of its
weighted fibre.