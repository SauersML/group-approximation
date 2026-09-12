---
rg: 2
id: weyl-kernel-joins-descend-two-levels-without-mass-contraction
kind: claim
title: The three Weyl kernel joins descend two levels but do not contract arbitrary isotypic mass
distinct_from:
  depth-shifted-regular-overlap-is-exactly-one-sixteenth: that computes a one-sixteenth overlap on a Plancherel block; this describes what the same kernel joins imply for arbitrary conductor weights.
  fixed-shift-invariance-does-not-force-flat-profile: that gives abstract asymptotically shift-invariant probability measures far from Haar; this identifies the exact arithmetic conductor descent which produces that shift invariance.
  lambda-exact-face-of-the-collapse-closes: that closes regular-type towers; this explains why its kernel argument cannot be iterated to close the scale-spread sector.
---

At level `2^a`, let `U_0` be the 16-element image `(DSO3)` of the shifted
kernel.  The three positive Weyl directions and their inverse directions
contain, between them,

```text
e_ij(2^(a-2))  for every i!=j.                         (WKD1)
```

Consequently their generated relative elementary subgroup is the depth
`a-2` principal congruence layer in `SL_3(Z/2^a)`.  Thus the Weyl interlock
does cover all root depths needed for a two-level conductor descent.

For an arbitrary finite-dimensional congruence representation, let
`S_(i,epsilon)` be the source-aligned common-quotient projections for the
three positive Weyl directions and their inverses.  If the same carrier is
aligned across these six orientations and the directional intertwining
defect is `eta`, property `(T)` and the exact Schur-support formula give

```text
1-tr(S_(i,epsilon)) <= (eta/epsilon_0)^2.               (WKD2)
```

Their intersection in the common source coordinate has trace at least

```text
1-6(eta/epsilon_0)^2                                  (WKD3)
```

and factors through level `a-2`.  Iterating a fixed number `N` of times gives
a subspace of trace `1-C_N eta^2` factoring through level `a-2N`.

This is not a contraction recurrence.  The factor `1/16` from `(DSO5)` is
the Plancherel dimension of the common quotient inside one regular top-level
block; an arbitrary representation may place all of its mass in that common
quotient.  In particular, choose `b_m->infinity` and `a_m-b_m->infinity`,
and inflate the regular representation of
`SL_3(Z/2^(b_m))` to level `2^(a_m)`.  These are canonical-trace
representations of `SL_3(Z)`, yet for every fixed `N` they already factor
through level `a_m-2N` for all large `m`.  Hence every fixed-depth conclusion
`(WKD3)` holds with full mass and gives no contradiction.

Equivalently, for arbitrary isotypic multiplicities the exact maximal common
fraction is

```text
(1/d) sum_tau dim(tau) min(m_A(tau),m_B(tau)),          (WKD4)
```

not the group-order ratio `1/16`.  It can equal one on a common shallow
quotient.  A scale-spread tower can move mass down the conductor filtration
without paying a fixed fraction, which is precisely the surviving solenoid
profile already recorded in `lambda-exact-face-of-the-collapse-closes`.

Therefore representation-ring descent alone cannot produce a `2^(-N)`
boundary after taking the microstate limit first.  Closing the remaining
two-primary exact sector requires a genuinely multiscale mixing/cocycle
estimate which charges transport between conductor bands, not another
one-step kernel-join count.
