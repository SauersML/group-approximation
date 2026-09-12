---
rg: 2
id: invertible-laurent-rank-compactness-counterexample-proof
kind: route
title: Use a cyclic shift and a geometric diagonal, then apply determinants
target: rank-zero-compactness-fails-for-invertible-laurent
requires: []
---

On the basis `e_0,...,e_(n-1)` of `Q^n`, let

```text
U_n e_i=e_(i+1 mod n),
V_n e_i=2^i e_i.
```

Both matrices are invertible.  For `0<=i<n-1`,

```text
V_n U_n e_i=2^(i+1)e_(i+1)=2U_n V_n e_i.
```

On `e_(n-1)` the two sides are respectively `e_0` and `2^n e_0`.
Thus their difference has image exactly the line `Q e_0`, proving `(RZC1)`.
Multiplication on either side by invertible matrices preserves rank, so the
Laurent residual in `(RZC2)` also has rank one.

If invertible `d`-by-`d` matrices over a characteristic-zero field solved
`VU=2UV` exactly, determinants would give

```text
det(VU)=2^d det(UV).
```

Since `det(VU)=det(UV)` is nonzero, this would imply `2^d=1`, impossible in
characteristic zero.  Hence no nonzero finite exact solution exists, while
the normalized defects `1/n` tend to zero.

