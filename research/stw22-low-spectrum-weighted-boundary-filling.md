---
rg: 2
id: stw22-low-spectrum-weighted-boundary-filling
kind: claim
title: Extend low-spectrum weighted sphere frames in every finite degree
distinct_from:
  stw22-hyperfinite-stiefel-all-sphere-fillings: that theorem fills unweighted spheres in a fixed corner; the present theorem preserves a fixed positive weight and a moving orthogonal target complement.
artifacts:
  - research/artifacts/stw22-low-spectrum-boundary-extension-audit-2026-08-30.md
---

Let `R` be the hyperfinite `II_1` factor, let `e in R` be a projection,
and fix an integer `m>=0`.  Suppose

```text
H:B^(m+1)->eR,       H(y)^*H(y)=p_h
```

is `2`-norm continuous, put `f(y)=e-H(y)H(y)^*`, and let `b in R_+`
satisfy

```text
0<=b<=eta,       p_l=supp(b),       tau(p_l)<=s,
tau(f(y))>=tau(p_l)       (y in B^(m+1)).
```

If `x:S^m->eR` is `2`-norm continuous and

```text
x(z)^*x(z)=b,       f(z)x(z)=x(z),
```

then there is a `2`-norm-continuous extension `X:B^(m+1)->eR` such that

```text
X|_(S^m)=x,       X(y)^*X(y)=b,       f(y)X(y)=X(y).    (LSW)
```

In particular the extension remains orthogonal to the filled high frame.
For every fixed `x_0` with `x_0^*x_0=b`, it also satisfies

```text
||X(y)-x_0||_2<=2 sqrt(tau(b))<=2 sqrt(eta s).          (LSB)
```

No ordinary-`2`-norm continuity of the boundary polar frames is assumed.
The proof splits `b` into countably many spectral bands bounded away from
zero, extends their continuous polar frames recursively into orthogonal
parts of the moving complement, and takes a uniform weighted `L^2` limit.
Thus the low-spectrum hinge in the weighted Stiefel transfer is closed in
every finite sphere degree, with the same norm bound.
