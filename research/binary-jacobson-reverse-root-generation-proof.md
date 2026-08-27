---
rg: 2
id: binary-jacobson-reverse-root-generation-proof
kind: route
title: Build one cross-block Weyl swap and move an arbitrary coefficient root everywhere
target: binary-jacobson-one-reverse-root-completes-two-target-parabolic
requires: []
artifacts:
  - notes/PROPERTY_T_FREE_MF_ATTEMPT_2026-08-26.md
---

The upper parabolic contains `x_14(1)`.  Together with the adjoined reverse
root it therefore contains the constant Weyl word

```text
w_14=x_14(1)x_41(1)x_14(1),                            (JREVP1)
```

which exchanges coordinates `1` and `4` in characteristic two.  The
constant Weyl groups already present on `I` and `Omega`, together with this
cross-block transposition, generate every permutation of the five
coordinates.

For every `r in J`, the group `P_+` contains `x_14(r)`.  Conjugating this
root by the constant Weyl representatives gives

```text
x_ij(r) in <P_+,x_41(1)>       for every i != j.        (JREVP2)
```

Again there are no coefficient signs over `F_2`.  The elements in `(JREVP2)`
are exactly the elementary generators of `EL_5(J)`, proving `(JREV1)`.

For a general reverse root `x_(alpha i)(1)`, conjugate first by the existing
active and target Weyl groups to reduce to `(alpha,i)=(4,1)`.  This proves
the final assertion.
