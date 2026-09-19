---
rg: 2
id: stw22-diffuse-relative-low-spectrum-disk-extension
kind: claim
title: Low-spectrum weighted loops extend through moving complements in every separable II1 factor
distinct_from:
  stw22-low-spectrum-weighted-boundary-filling: that theorem works in the hyperfinite factor in every finite sphere degree; the present theorem works in an arbitrary separable II1 factor in the degree-one disk case needed for two-dimensional selection.
  stw22-diffuse-stiefel-uniform-loop-fillings: that theorem fills projection-weight loops in a fixed target corner; the present theorem preserves an arbitrary positive weight while the available target projection moves over the filling disk.
artifacts:
  - research/artifacts/stw22-dim2-arbitrary-factor-breakthrough-2026-08-30.md
---

Let `(N,tau)` be a II1 factor with separable predual, let `e in N` be a
projection, and let

```text
H:D^2 -> eN,        H(y)^*H(y)=p_h
```

be `2`-norm continuous. Put `f(y)=e-H(y)H(y)^*`. Let `b in N_+`
be a contraction with support `p_l`, and assume the strict trace slack

```text
tau(p_h)+tau(p_l) < tau(e).                              (DR1)
```

If `x:S^1->eN` is `2`-norm continuous and

```text
x(z)^*x(z)=b,        f(z)x(z)=x(z),                      (DR2)
```

then there is a `2`-norm-continuous extension `X:D^2->eN` satisfying

```text
X|_(S^1)=x,          X(y)^*X(y)=b,        f(y)X(y)=X(y). (DR3)
```

If `0<=b<=eta`, then for every fixed `x_0` with
`x_0^*x_0=b` the extension automatically obeys

```text
||X(y)-x_0||_2 <= 2 sqrt(tau(b))
                 <= 2 sqrt(eta tau(p_l)).                (DR4)
```

No continuity of the support or polar frame of `b` is assumed. The strict
slack in `(DR1)` is retained at every spectral-band stage; it is what makes
the moving-corner Stiefel family uniformly equi-`LC^1`.
