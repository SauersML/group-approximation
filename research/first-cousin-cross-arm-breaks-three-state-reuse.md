---
rg: 2
id: first-cousin-cross-arm-breaks-three-state-reuse
kind: claim
title: One cousin cross-arm row breaks three-state reuse but only demands one fresh Pauli factor
distinct_from:
  full-prefix-range-cells-have-three-state-model: that realizes every local parent/range and sibling crossed-zero cell on twelve dimensions; this adds the first equal-depth cross-address inverse row between two colliding cousin cells.
  leavitt-prefixes-form-exponential-heisenberg-packet: that gives the complete exact prefix pairing and its exact finite-dimensional capacity; this isolates one collision detector and audits whether the whole pairing can be compiled from finitely many lossless prototypes.
  level-synchronous-first-mismatch-area-is-centralizer-impossible: that proves the complete equal-level mismatch table cannot have uniform filling area; this combines that obstruction with the finite fresh-factor model and the operator-norm packing endpoint.
artifacts:
  - research/first-cousin-cross-arm-proof.md
---

**ESTABLISHED SMALLEST COLLISION TEST; FINITE ESCAPE AND UNIFORM-AREA
FIREWALL.**  At one common prefix depth, let

```text
X_alpha=x_12(t_alpha),       Z_beta=x_23(s_beta),
J=x_13(A).
```

The first genuinely cross-address row is

```text
[X_alpha,Z_beta]=1                         (alpha!=beta), (CCA1)
```

retained together with the two diagonal rows

```text
[X_alpha,Z_alpha]=[X_beta,Z_beta]=J.                   (CCA2)
```

Choose two equal-depth addresses whose cells collide in the three-state
prefix model, for example the `00` and `11` character states.  Reusing the
same Pauli factor makes the left side of `(CCA1)` equal to `J`, so this one
row detects the twelve-dimensional periodic assignment.

It does not imply `(BAC1)`.  Give `alpha` and `beta` two fresh Pauli factors,
both controlled by the prescribed `J=-1` projection.  Then `(CCA1)--(CCA2)`
and all local parent/range cells are exact while the mark survives.  More
generally every finite depth-`n` complete prefix table has an exact marked
model obtained by assigning one Pauli factor to each of the `2^n` leaves.
The required dimension grows, but there is no defect floor at any fixed
depth.

Keeping **all** cousin cross rows would supply the desired finite-capacity
soundness: `opnorm-pauli-cross-check-packing-capacity` makes the minimum
dimension tend to infinity with the number of leaves.  However those
canonical cross rows cannot be losslessly controlled by finitely many fixed
null prototypes.  Such control would give a uniform relator-area bound for
the equal-level first-mismatch table, contradicting
`level-synchronous-first-mismatch-area-is-centralizer-impossible`.

Hence the smallest cross-address holonomy has now been located, but it
exposes a dichotomy rather than closing the compiler:

```text
finitely many cousin rows       exact fresh-factor marked model;
all growing cousin rows         capacity, but no uniform prototype area.
                                                               (CCA3)
```

A viable atomic prototype must compress the growing cousin table into a
different fixed nonlinear holonomy.  It cannot simply request the canonical
prefix cross-zero commutators one pair at a time.

No Property `(T)`, Kazhdan input, stability theorem, or literature result is
used.

DERIVATION
first-cousin-cross-arm-proof
