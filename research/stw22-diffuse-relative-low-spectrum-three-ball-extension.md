---
rg: 2
id: stw22-diffuse-relative-low-spectrum-three-ball-extension
kind: claim
title: Low-spectrum weighted two-spheres extend through moving complements in every separable II1 factor
distinct_from:
  stw22-diffuse-relative-low-spectrum-disk-extension: that theorem is the relative degree-one disk case; the present theorem is the degree-two three-ball case.
  stw22-low-spectrum-weighted-boundary-filling: that theorem works in every degree only for the hyperfinite factor; the present theorem treats arbitrary separable-predual II1 factors in degree two.
artifacts:
  - research/artifacts/stw22-dim3-diffuse-bundle-breakthrough-2026-08-30.md
---

Let `(N,tau)` be a II1 factor with separable predual, let `e in N` be
a projection, and let

```text
H:B^3 -> eN,        H(y)^*H(y)=p_h
```

be `2`-norm continuous. Put `f(y)=e-H(y)H(y)^*`. Let `b in N_+`
be a contraction with support `p_l`, and assume

```text
tau(p_h)+tau(p_l)<tau(e).                               (TR1)
```

If `x:S^2->eN` is `2`-norm continuous and

```text
x(z)^*x(z)=b,       f(z)x(z)=x(z),                      (TR2)
```

then there is a `2`-norm-continuous extension `X:B^3->eN` satisfying

```text
X|_(S^2)=x,         X(y)^*X(y)=b,       f(y)X(y)=X(y).  (TR3)
```

If `0<=b<=eta`, every such extension obeys, for a fixed
`x_0^*x_0=b`,

```text
||X(y)-x_0||_2<=2 sqrt(tau(b))
                <=2 sqrt(eta tau(p_l)).                 (TR4)
```

No polar frame on `supp(b)` is selected. The theorem is diffuse only:
every moving nonzero corner is a II1 factor; no matrix analogue is asserted.
