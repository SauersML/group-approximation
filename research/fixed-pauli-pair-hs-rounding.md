---
rg: 2
id: fixed-pauli-pair-hs-rounding
kind: claim
title: One approximate Pauli pair rounds inside any residual matrix algebra with a universal modulus
distinct_from:
  quantum-expander-rounds-relative-pauli-cell: that first moves a pair into a growing spin factor's commutant; this is only the fixed residual D8 table after that movement has occurred.
---

There are absolute constants `C,epsilon_0>0` such that, in every matrix
algebra `M_r`, two contractions which are within `epsilon<=epsilon_0` in
normalized Hilbert--Schmidt norm of being self-adjoint involutions and satisfy

```text
||PQ+QP||_2<=epsilon
```

can, after the standard flexible addition or deletion of `O(epsilon^2 r)`
dimensions, be changed by at most `C epsilon` to exact self-adjoint
involutions `P_0,Q_0` with `P_0Q_0=-Q_0P_0`.  The constants are independent
of `r` and of any external tensor factor.

