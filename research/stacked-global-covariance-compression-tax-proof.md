---
rg: 2
id: stacked-global-covariance-compression-tax-proof
kind: route
title: Expand every compressed row and take the Hilbert direct-sum norm
target: stacked-global-covariance-has-unit-compression-tax
requires: []
---

From `(SCT1)--(SCT2)`,

```text
d_c=(a_cv_c-v_cZ)Q+v_c(ZQ-QZ)=g_cQ+v_c[Z,Q],
```

which is `(SCT3)`.  If `g_c=0`, left multiplication by the unitary `v_c`
preserves normalized Hilbert--Schmidt norm, proving `(SCT4)`.

For `(SCT5)`, orthogonality of the target summands gives

```text
S^*S=N^(-1) sum_c Qv_c^*v_cQ=Q.
```

Under exact global covariance, the `c`-th component of `AS-SZ` is
`N^(-1/2)v_c[Z,Q]`.  Pythagoras proves `(SCT6)`.

Finally regard `(d_c)_c`, `(g_cQ)_c`, and `(v_c[Z,Q])_c` as vectors in the
Hilbert direct sum of `N` matrix `L^2` spaces.  The last vector has norm
`sqrt(N)||[Z,Q]||_2`, while the middle vector has norm at most
`(sum_c||g_c||_2^2)^(1/2)`.  The reverse and ordinary triangle inequalities
give `(SCT7)` and its upper counterpart.

