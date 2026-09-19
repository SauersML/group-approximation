---
rg: 2
id: stw22-transfer-all-sphere-fillings-to-weights-proof
kind: route
title: Transfer all finite Stiefel sphere fillings through high-low spectral decompositions
target: stw22-weighted-purification-all-sphere-fillings
requires:
  - stw22-hyperfinite-stiefel-all-sphere-fillings
  - stw22-low-spectrum-weighted-boundary-filling
artifacts:
  - research/artifacts/stw22-all-degree-weighted-selection-audit-2026-08-30.md
---

Fix `k>=0` and `epsilon>0`.  Choose `eta>0` so that

```text
2sqrt(eta s)<epsilon/3.                                (AW1)
```

For a fixed weight `a`, put

```text
p_h=1_[eta,1](a),       p_l=supp(a)-p_h,
a_l=ap_l.
```

Let `w:S^k->F(a)` have image in a `rho`-ball about
`w_0=v_0a^(1/2)`.  The high polar frame is defined directly by

```text
v_h(z)=w(z)a^(-1/2)p_h
```

and is continuous because the inverse square root is bounded on `p_h`.
Moreover

```text
||v_h(z)-v_0p_h||_2
 <=eta^(-1/2)||w(z)-w_0||_2.                           (AW2)
```

Choose `rho` so that `(AW2)` is below the input modulus from
`stw22-hyperfinite-stiefel-all-sphere-fillings` for output radius
`epsilon/3`.  Fill `v_h` by

```text
V_h:B^(k+1)->V(p_h,e)
```

within `epsilon/3` of `v_0p_h`.  Put
`f(y)=e-V_h(y)V_h(y)^*`.  The continuous weighted low boundary field

```text
x(z)=w(z)p_l
```

satisfies `x(z)^*x(z)=a_l` and `f(z)x(z)=x(z)`.  The all-degree form of
`stw22-low-spectrum-weighted-boundary-filling` extends it to

```text
X_l:B^(k+1)->eR,
X_l^*X_l=a_l,       fX_l=X_l,
```

with its exact boundary.  Now set

```text
W(y)=V_h(y)a^(1/2)p_h+X_l(y).                           (AW3)
```

Orthogonality gives `W(y)^*W(y)=a`, and `(AW3)` has boundary `w`.
The high part moves by less than `epsilon/3`, while the low part is within
`2sqrt(eta s)<epsilon/3` of `v_0a^(1/2)p_l`.  Hence the filling stays in
the `epsilon`-ball about `w_0`.

The input radius depends only on `k,epsilon,s,e`, not on `a`.  The global
metric-uniform filling statement implies Michael's ambient-local
equi-`LC^k` condition: a sphere in a sufficiently small ambient ball has
diameter at most twice that radius, and the preceding filling remains near
one chosen point of its image.

Finally take an arbitrary map `S^k->F(a)`.  Its high frame is still
continuous and fills because each fixed strong Stiefel space is
`k`-connected.  Apply the same all-degree low weighted extension and
formula `(AW3)`, without the radius estimates.  Thus every `F(a)` is
`k`-connected.
