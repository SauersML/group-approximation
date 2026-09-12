---
rg: 2
id: support-return-native-loop-proof
kind: route
title: Use prefix supports to return both converted arms and factor the native Whiteheads
target: support-return-gives-gauged-native-loop
requires:
  - minimal-t00-conversion-cannot-return-native-whitehead-root
  - external-group-misses-native-t00-roots
  - native-whitehead-hecke-head-has-order-seven-anchor
  - recentered-order-seven-heads-have-actor-holonomy
---

The composable root paths in `(SRL2)` are `(8,9)(9,7)=(8,7)` and
`(9,7)(7,8)=(9,8)`.  Their coefficients are `x_1t_00=y_2` and
`t_00x_2=y_1`, proving the two commutator identities.

For a projection `e`, the characteristic-two partial Whitehead
`W_ab(e,e)` swaps the `e`-supported pieces of coordinates `a,b` and fixes
their complements.  Apply this block matrix first on the right-supported
roots `Z_1,H_2` and then on the left-supported roots `H_1,Z_2`.  The four
prefix cancellations in `(SRL4)` give `(SRL5)` entry by entry.  Multiplying
the three returned factors and cancelling adjacent `W_i^2=1` gives
`(SRL6)`.

The exact artifact verifies the more general formulas

```text
W_(ell,9)(e_000)x_(8,ell)(y_2)W_(ell,9)(e_000)=x_89(y_2),
W_(ell,7)(e_0)x_(ell,8)(y_1)W_(ell,7)(e_0)=x_78(y_1)   (SRLP1)
```

for all five actor spare endpoints in each row.  It also verifies the two
forward-arm returns used in `(SRL5)`.

Finally close the signed pair `L_0,lambda_0` exactly and apply the full ten
generator conjugacy signature to both support Whiteheads, all four native
factor roots, and both complete `J_i`.  Every preservation test is false.
This proves the signed-cut assertion independently of the recentered-center
commutation argument.

For the same-center audit, close the six named Pauli root generators by
exact Leavitt-matrix multiplication.  The closure has `128` elements.
Conjugate each generator by `W_1,W_2`, the two inner cross-depth
Whiteheads, and `J_1,J_2`, and compare using faithful prefix equality rather
than syntactic normal-form equality.  The resulting six-bit membership
rows are exactly `(SRL7)`.  Since `J_i=W_i(Z_iH_iZ_i)W_i`, the inner word
normalizes the conjugate chart `W_iEW_i` even though it does not normalize
`E`; its action there is conjugate to the nonidentity adjacent swap.
