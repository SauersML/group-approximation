---
rg: 2
id: mf-root-transport-is-vacuous-on-leavitt-units
kind: claim
title: The operator-MF root transport certifies no Leavitt coefficient
invalidates: [kl-leavitt-holds-via-mf-root-transport]
distinct_from:
  binary-leavitt-all-ranks-full-mf-radical: that is the full-radical theorem itself; this records its exact consequence for the matrix-root proof of Kervaire--Laudenbach over the same group.
  kervaire-laudenbach-holds-for-mf: that proves injectivity for MF coefficient groups; this says the same argument has nothing to extend over the Leavitt unit group.
---

Let `G = L_(F_2)(1,2)^x`.  Every homomorphism from `G` into the unitary group
of a norm matrix corona is trivial.  Consequently the extension argument of
`nonsingular-adjunction-preserves-approximation-radicals`, run with norm
coronas as targets, extends only the trivial map, and certifies injectivity of
no coefficient for any nonsingular equation over `G`.  In particular the
operator-MF proof of `kervaire-laudenbach-holds-for-mf` does not apply to `G`.
For a subgroup `K <= G` containing a copy of some `EL_n(L)`, that copy lies in
`Rad_MF(K)`, so the same transport certifies no element of it.

Any positive Kervaire--Laudenbach proof over `G` by approximation must
therefore use tracial targets.
