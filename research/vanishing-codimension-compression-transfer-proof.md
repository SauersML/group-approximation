---
rg: 2
id: vanishing-codimension-compression-transfer-proof
kind: route
title: Lift the compressed witness and apply property T before returning to the corner
target: vanishing-codimension-compressions-obey-projective-transfer
requires:
  - exact-projective-codensity-has-a-uniform-trace-square-gap
---

Write `d=dim(H)`, `r=d-rank(P)`, and use normalized Hilbert--Schmidt norm on
`M_d`.  For every unitary `T`,

```text
||(I-P)TP||_2^2 <= r/d,
||PTP - polar(PTP)||_(2,P) <= O(sqrt(r/d)).             (VPP1)
```

The first bound follows by moving `T` across the trace and bounding by
`tau(I-P)`; the second is the standard polar correction estimate applied to
`(PTP)^*(PTP)-P=-PT^*(I-P)TP`.  Hence all fixed compressed words differ from
their polar-corrected words by `O(sqrt(r/d))`.

Extend `U` by zero to `V=PUP in M_d`.  The fixed perfectness/telescoping
argument `(PTS4)` removes the scalar phases in `(VCP2)`.  Combining it with
`(VPP1)` gives

```text
max_(c in S_C)||V pi(c)-pi(c)V||_2
 <= O(sqrt(sum_c E_c)+sqrt(r/d)).                       (VPP2)
```

Apply property (T) to the exact conjugation representation of `C` on
`M_d`.  The vector `V` is within the right side of `(VPP2)`, divided by the
fixed Kazhdan constant, of `pi(C)'`.  Finite-dimensional co-density for this
arithmetic pair gives

```text
pi(C)'=pi(A)',                                         (VPP3)
```

so the corrected vector commutes with `pi(h)`.  Therefore
`||[V,pi(h)]||_2` has the same bound.  Compress back to `PH`, use `(VPP1)`
for `h`, and square the estimate.  The identity

```text
1-|tr(W)|^2 <= ||W-I||_2^2
```

then gives `(VCP4)`.
