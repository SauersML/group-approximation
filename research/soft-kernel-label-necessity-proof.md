---
rg: 2
id: soft-kernel-label-necessity-proof
kind: route
title: Compare the HS kernel with the regular-label Hamming kernel
target: nonsofic-block-monomial-images-force-soft-kernel-labels
requires: []
---

Apply the regular action `(UDB3)` coordinatewise.  Its Hamming identity
length is exactly `(SBL3)`.  Formula `(BLR3)`, which does not require a
uniform gap, always gives

```text
(1/2)||A-1||_2^2 <= 2 h_n(A).                           (SKL1)
```

Therefore Hamming-trivial sequences are HS-trivial.  The regular actions
descend to an injective permutation-ultraproduct representation of
`H=F_0/N_2` exactly when the reverse implication holds on every fixed
`w in N_2`; this is `(SBL4)`.  If `(SBL4)` held and `H` were nonsofic, that
embedding would be a contradiction.  Countability and the ultrafilter then
give one fixed `w` and `alpha>0` satisfying `(SBL5)`.

Because `w in N_2`, the left side of `(BLR3)` tends to zero.  Its nonnegative
base-motion and label-energy terms therefore tend separately to zero, giving
`(SBL6)--(SBL7)`.  Markov's inequality shows that the density of fixed-base
labels with character gap at least `eta` tends to zero.  After `(SBL6)`, at
least `alpha-o(1)` of the activity in `(SBL5)` comes from nonidentity labels
on fixed base blocks.  Removing the `eta`-hard labels leaves `(SBL8)` with
lower ultralimit density at least `alpha`.
