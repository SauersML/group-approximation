---
rg: 2
id: stw22-diffuse-weighted-loop-transfer-proof
kind: route
title: Transfer diffuse Stiefel loop fillings across the low spectrum
target: stw22-diffuse-weighted-purification-uniform-loop-fillings
requires:
  - stw22-diffuse-stiefel-uniform-loop-fillings
  - stw22-diffuse-relative-low-spectrum-disk-extension
artifacts:
  - research/artifacts/stw22-dim2-arbitrary-factor-breakthrough-2026-08-30.md
---

Nonemptiness and closedness of the fibres, and lower semicontinuity of
`a |-> F_e(a)`, are factor-independent. The weighted Bures lifting
argument in `stw22-cross-stratum-selection-in-dimension-one-proof` applies
verbatim: align a high spectral cut by polar decomposition, put its small
missing initial support into the fixed trace slack `tau(e)-s`, and send
the low spectral mass arbitrarily inside the remaining corner.
Powers--Stoermer then makes the lifted weighted frames converge in
`2`-norm. Principal-log unitary paths give path connectedness and the
uniform equi-`LC^0` part.

Fix `epsilon>0`. Choose `eta>0` so that

```text
2 sqrt(eta s)<epsilon/3.                                (DW2)
```

For a fixed weight `a`, put

```text
p_h=1_[eta,1](a),       p_l=supp(a)-p_h.                 (DW3)
```

Let `w:S^1->F_e(a)` lie in a sufficiently small ball about
`w_0=v_0a^(1/2)`. The high polar frame

```text
v_h(z)=w(z)a^(-1/2)p_h
```

is continuous and satisfies

```text
||v_h(z)-v_0p_h||_2
 <=eta^(-1/2)||w(z)-w_0||_2.                            (DW4)
```

After identifying its fixed initial projection with the range of
`v_0p_h` in `eNe`, apply
`stw22-diffuse-stiefel-uniform-loop-fillings` in that corner. For a
uniformly small input radius, it gives a filling

```text
H:D^2->eN,       H^*H=p_h,
```

whose high frame remains within `epsilon/3` of `v_0p_h`.

On the boundary, the low weighted frame `x(z)=w(z)p_l` has fixed weight
`b=ap_l` and range in the complement of `v_h(z)). Moreover

```text
tau(p_h)+tau(p_l)<=s<tau(e).
```

The relative theorem
`stw22-diffuse-relative-low-spectrum-disk-extension` therefore extends
`x` through the moving complement of `H`. Call the extension `X` and
put

```text
W(y)=H(y)a^(1/2)p_h+X(y).                               (DW5)
```

Orthogonality gives `W^*W=a` and the boundary is exactly `w`. The high
part of `(DW5)` moves by less than `epsilon/3`, while `(DR4)` and
`(DW2)` bound the entire low part by another `epsilon/3`. Thus the
filling remains in the prescribed `epsilon`-ball. The input radius comes
only from `epsilon,eta,e,s`, so it is independent of `a`.

For an arbitrary loop, the same construction is used without radius
bounds. The high Stiefel loop is null-homotopic: lift it over `S^1` using
Farah--Vaccaro's one-dimensional comparison theorem and contract the
unitary loop by Jekel's Theorem A. The relative low-spectrum theorem then
finishes `(DW5)`. Hence every fibre is simply connected.

The family now satisfies the `n=1` hypotheses of Michael's
*Continuous Selections II*, Theorem 1.2. Applying it to
`x |-> F_e(a(x))` over any compact Hausdorff `X` with `dim(X)<=2`
produces the asserted global weighted purification.
