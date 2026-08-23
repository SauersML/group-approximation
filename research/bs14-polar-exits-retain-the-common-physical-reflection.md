---
rg: 2
id: bs14-polar-exits-retain-the-common-physical-reflection
kind: claim
title: BS14 polar source extraction retains both exit equations against the same physical involution
distinct_from:
  common-physical-reflection-pays-two-exit-gram-seam: that turns these two exit errors into the mixed Gram identity; this asks for the errors from the actual cubic polar extraction.
  two-cubic-residual-carriers-recover-the-deleted-source: that identifies a common source inside exact positive-corner carriers under transversality; this asks for quantitative forward/backward transport by the supplied near tuple after source alignment and active/passive thresholding.
  bs14-residual-polar-data-build-active-dilation: that includes the later Gram completion, integer cells, and endpoint authentication; this is only the continuous physical-exit row.
---

In the setup of
`bs14-residual-polar-data-build-active-dilation`, let `V` be the common
source isometry obtained after the two polar source maps are aligned, let
`P=1-VV^*`, and put

```text
U_1=S^2,                    U_2=RS,
F_i=P U_iV,                H_i=P U_i^(-1)V.           (PER1)
```

After rounding the supplied `X` to a physical reflection and paying the
source alignment and passive deletion, prove

```text
sum_(i=1)^2 ||X F_i-H_i||_F^2/d ->0                  (PER2)
```

with one dimension-independent modulus in the original four-relator
energy.

In fact no detailed SVD covariance is required.  If `e` is the normalized
four-relator energy and the high-residual threshold is

```text
theta=c e^(1/4),
```

then the common active source dimension `r=dim E` satisfies

```text
r/d <= c^(-2)e^(1/2).                                (PER3)
```

Consequently

```text
sum_i ||XF_i-H_i||_F^2/d
 <=8r/d
 <=8c^(-2)e^(1/2).                                   (PER4)
```

Thus even if polar alignment loses the literal exit equation, the entire
loss is confined to the already energy-paid active source rank.  Rounding
`X` to a reflection does not affect the estimate because only unitarity and
contractivity are used.

The phrase “each polar row is individually compatible” is insufficient:
it permits a different reflection for each row.  Equation `(PER2)` requires
both rows to retain the same physical `X`.  Once `(PER2)` holds,
`common-physical-reflection-pays-two-exit-gram-seam` proves the mixed moment
`V^*S^(-3)V-V^*S^6V` tends to zero, and the joint Gram-swap completion
applies on an `o(d)` surgery hull.
