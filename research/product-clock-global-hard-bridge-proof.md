---
rg: 2
id: product-clock-global-hard-bridge-proof
kind: route
title: Conjugate one bridge by the commuting Fanizza and Thompson clocks
target: product-clock-global-hard-bridge-has-finite-orbit
requires:
  - thompson-site-pulses-localize-hard-exits
  - gauge-covariant-hard-shares-admit-site-bridges
---

Use the usual Thompson generator with prefix action

```text
0 xi -> 00 xi,       10 xi -> 01 xi,       11 xi -> 1 xi.
```

Starting at `x_0=10 infinity` gives `g^n x_0=0^n10 infinity`, so the sites are
distinct and their addresses have linear length.

Because the source group and pulse factors commute, conjugation by
`T_r^n=(Ug_r)^n` sends the two sides of `(PGB1)` to

```text
a_(r,n)u_(r,n)          and          u_(r,n)A_(r,n),
```

respectively.  This proves `(PGB6)`.  Reordering `(Ug_r)^n` into `U^ng_r^n`
uses `O(n^2)` applications of the fixed cross commutators, so this identity
has polynomial area in the finite presentation.

The rational-tail action of `V_r` has two ordered-pair orbits.  Relations
`(PGB2)--(PGB3)` therefore give

```text
[g_r^n u_(r,0)g_r^-n,B_(r,k)]=1                       (1)
```

whenever `k!=n`.  Standard prefix-table transporters and point-stabilizer
normal forms have polynomial length, so `(1)` has polynomial area in `n+k`.
Since `U` commutes with all pulse words, conjugating `(1)` by `U^n` proves
the same-role part of `(PGB7)`.  The different-role part follows from
`(PGB4)` and the direct-product cross relations, again with polynomial word
and area cost.  There are only finitely many roles.

For exact completeness, gauge covariance conjugates each `A^(r)` to its
negative, so its positive and negative spectral spaces have equal
multiplicity.  The local source sign `a_(r,0)` is balanced in the doubled
pulse packet.  After common amplification the two involutions are unitarily
conjugate; choose such a conjugating unitary as `u_(r,0)`.  It acts only on
the original marked factor and the `r`th base-site factor.  A Thompson point
stabilizer permutes only the other site factors, and all other role factors
are disjoint, proving `(PGB2)--(PGB4)` in the exact model.

Finally, if a derived relation has area `D`, telescoping its van Kampen
derivation bounds its normalized-HS defect by `D sqrt(E)`, where `E` is the
total named squared relator energy.  Since `D` is polynomial here, feeding
these estimates into `(PPB6)` gives one polynomial prefix-leakage modulus,
independent of matrix dimension.
