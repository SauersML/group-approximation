---
rg: 2
id: quantum-expander-rounds-relative-pauli-cell
kind: claim
title: Expander commutant rounding reduces a growing Clifford extension to one fixed Pauli cell
distinct_from:
  finite-schur-clifford-packet-flexible-hs-exactification: that exactifies the entire finite packet with constants depending on its size; this assumes an exact old spin factor and obtains a constant independent of its rank.
---

Fix `lambda<1` and `D`. There is a dimension-independent modulus with the
following property. Suppose an exact old spin factor `M_N tensor I_r` is
equipped with a `D`-regular quantum-expander set `U_j tensor I_r` of gap
`1-lambda`, and matrices `P,Q` are approximate self-adjoint involutions which

1. approximately commute with all `U_j tensor I_r`, and
2. approximately satisfy the one-cell Pauli relation `PQ=-QP` (or its marked
   central-sign version).

After discarding or flexibly adding `O(delta^2 Nr)` dimensions, the tuple is
`O_(D,lambda)(delta)`-close to one in which

```text
P=I_N tensor P_0,             Q=I_N tensor Q_0,
```

and `(P_0,Q_0)` is an exact Pauli pair on the residual factor. The constants
do not depend on `N`.
