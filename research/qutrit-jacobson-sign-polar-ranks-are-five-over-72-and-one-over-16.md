---
rg: 2
id: jacobson-sign-polar-ranks-are-five-over-72-and-one-over-16
kind: claim
title: Jacobson sign-quarter polar ranks are 5/72 and 1/16, not their overlap energy
artifacts:
  - research/qutrit-jacobson-sign-polar-rank-proof.md
distinct_from:
  qutrit-complementary-jacobson-signs-with-minimal-router-are-finite: that gives the finite regular model and exact common-router recombination; this diagonalizes the relevant 288-element subgroup and computes every cut-down polar rank.
  qutrit-first-mixed-orientation-head-return-is-jacobson-quarter-polar: that computes the nested projections and their overlap energies; this corrects the missing rank calculation for their qutrit cuts.
  weighted-unitary-hall-deficit-gap: that turns an authenticated source-target rank deficit into a terminal; this supplies the exact source ranks which a future mixed router would have to preserve.
---

Let

```text
G_(sigma,tau)=E(1+sigma C_1)(1+tau W)/4,
R=e_0+e_1.
```

Although

```text
||G_(sigma,tau)R||_2^2=1/36                            (QPR1)
```

for all four signs, the initial support of the polar of
`G_(sigma,tau)R` is larger. In the canonical group trace,

```text
tau(supp|G_(+,+)R|)=5/72,
tau(supp|G_(sigma,tau)R|)=1/16
                         for (sigma,tau)!=(+,+).         (QPR2)
```

The same numbers are the range-support traces.

These ranks are computed in the finite subgroup

```text
F_0=<C,H,C_1,W>
   isomorphic to C_2 times C_3 times (F_2^4 semidirect C_3),
|F_0|=288.                                               (QPR3)
```

The quotient `C_3` acts fixed-point-freely and diagonally on two copies
of its irreducible two-dimensional `F_2` module. The trivial sign has
regular rank `20` after the two selected central-character blocks are
included; every nontrivial sign has rank `18`. Dividing by `288` gives
`(QPR2)`.

This sharpens the Hall burden. The one-complement target has

```text
tau(Ee_2)=1/18=4/72.                                    (QPR4)
```

Thus an occurrence which transported the full polar of one sign branch
into `Ee_2` would have a strict deficit:

```text
(+,+) gap:       5/72-4/72=1/72,
other gap:       1/16-1/18=1/144.                       (QPR5)
```

No such transport is asserted here. The finite minimal-router model
proves that `e_2g_1G_(sigma,tau)R` loses source support. The result
identifies the exact next target: prove that a `g_2`-conditioned raw
`S/T` relation preserves one of the source supports in `(QPR2)` while
forcing its range into `Ee_2`. Energy `(QPR1)` alone is insufficient.
