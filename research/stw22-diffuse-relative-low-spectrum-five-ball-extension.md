---
rg: 2
id: stw22-diffuse-relative-low-spectrum-five-ball-extension
kind: claim
title: Low-spectrum weighted four-spheres extend through moving complements in every separable II1 factor
distinct_from:
  stw22-diffuse-relative-low-spectrum-four-ball-extension: that theorem is one degree lower; the present theorem uses degree-four Stiefel control over a five-ball.
artifacts:
  - research/artifacts/stw22-dim5-factor-bundle-breakthrough-2026-08-31.md
---

Let `(N,tau)` be a separable-predual II1 factor, `e in N` a projection,
and `H:B^5->eN` continuous with `H^*H=p_h`. Put `f=e-HH^*`. Let `b`
be a positive contraction with support `p_l` and

```text
tau(p_h)+tau(p_l)<tau(e).                              (R5-1)
```

Every continuous boundary map `x:S^4->eN` with `x^*x=b` and `fx=x`
extends to `X:B^5->eN` with the same equations. If `b<=eta`, then for
any fixed `x_0^*x_0=b`,

```text
||X(y)-x_0||_2<=2sqrt(tau(b))<=2sqrt(eta tau(p_l)).    (R5-2)
```