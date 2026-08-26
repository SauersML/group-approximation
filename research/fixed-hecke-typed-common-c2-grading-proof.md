---
rg: 2
id: fixed-hecke-typed-common-c2-grading-proof
kind: route
title: Check the mod-two incidence of every carrier-valid native row
target: fixed-hecke-typed-interface-has-common-c2-grading
requires:
  - cross-row-native-diamond-cube-retains-common-c2-gauge
  - named-odd-native-factor-rows-have-no-esb-common-carrier
  - endpoint-whitehead-star-braid-synchronizes-native-gauges
---

Give each occurrence in

```text
S={J_1,J_2,B_2,B_3,W}
```

degree one in `F_2`, and give every other named occurrence degree zero.  It
suffices to check that the two sides of every carrier-valid defining row
have the same degree.

For the native head factorizations,

```text
deg(J_iB_(i+1)A_i)=1+1+0=0=deg(T_i).
```

The seventh-power rows then have degree zero.  Involution rows have degree
two.  A conjugacy or commutator row containing `J_i`, `B_i`, or `W` as its
actor contains that actor once positively and once inversely, so its total
degree is zero.  This covers the Pauli sign flips, the native-arm diamonds,
their cross-row commutators, and their named naturality consequences.

For any Coxeter row between two degree-one Whiteheads `X,Y`,

```text
XYX=YXY,
```

both sides have degree three, hence degree one.  This applies to the
`J_1--J_2`, `J_1--W`, and `J_2--W` braids.  Thus the endpoint rows synchronize
the three gauges but do not kill their common value.  All authenticated
positive-return rows use only degree-zero factors, or use a degree-one actor
twice in a covariance square, and are homogeneous as well.

Hence the degree map on the free occurrence group annihilates every
carrier-valid relator and descends to a homomorphism onto `C_2`; it is onto
because the image of `J_1` is nontrivial.  Every relation derived from this
interface lies in the kernel of the degree map.  In particular, a relation
equating an odd-grade native transport with a degree-zero ungauged
coefficient bridge cannot be derived from it.

The global odd rows listed in
`named-odd-native-factor-rows-have-no-esb-common-carrier` are not relators of
this carrier-local occurrence group: at least one of their factors acts
between a different chart or has no authenticated compression on the fixed
carrier.  Adding such a row before proving its source/range Gram would be
exactly the occurrence-typing error that `(ESB1)--(ESB2)` are designed to
exclude.
