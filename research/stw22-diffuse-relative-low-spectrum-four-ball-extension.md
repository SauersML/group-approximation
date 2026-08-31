---
rg: 2
id: stw22-diffuse-relative-low-spectrum-four-ball-extension
kind: claim
title: Low-spectrum weighted three-spheres extend through moving complements in every separable II1 factor
distinct_from:
  stw22-diffuse-relative-low-spectrum-three-ball-extension: that theorem is the relative degree-two case; the present theorem uses degree-three Stiefel control over a four-ball.
  stw22-low-spectrum-weighted-boundary-filling: that theorem is all-degree but hyperfinite; the present theorem treats arbitrary separable-predual II1 factors in degree three.
artifacts:
  - research/artifacts/stw22-dim4-factor-bundle-breakthrough-2026-08-31.md
---

Let `(N,tau)` be a II1 factor with separable predual, let `e in N` be a
projection, and let

```text
H:B^4->eN,        H(y)^*H(y)=p_h
```

be `2`-norm continuous. Put `f(y)=e-H(y)H(y)^*`. Let `b in N_+` be a
contraction with support `p_l`, and assume

```text
tau(p_h)+tau(p_l)<tau(e).                              (TR4-1)
```

If `x:S^3->eN` is continuous and

```text
x(z)^*x(z)=b,       f(z)x(z)=x(z),                     (TR4-2)
```

then there is a continuous extension `X:B^4->eN` satisfying

```text
X|_(S^3)=x,         X(y)^*X(y)=b,       f(y)X(y)=X(y). (TR4-3)
```

If `0<=b<=eta`, then, for any fixed `x_0^*x_0=b`,

```text
||X(y)-x_0||_2<=2sqrt(tau(b))
                <=2sqrt(eta tau(p_l)).                 (TR4-4)
```

The theorem is diffuse only and makes no matrix assertion.