---
rg: 2
id: odd-leavitt-reflections-retain-stationary-xor-overlap
kind: claim
title: Odd Leavitt reflection words retain an exact stationary XOR overlap sector
distinct_from:
  odd-leavitt-steinberg-reflection-prerequisites: that proves finite presentation, literal reflection words, signed connector transport, and the common p-phase theorem; this proves that those new words still forget projection inclusion in abstract unitary representations.
  fanizza-reflection-recurrence-has-s4-stationary-overlap: that gives the same smallest affine Boolean group for Fanizza's doubling shadow; this applies it to literal odd-characteristic Leavitt prefix reflections and the one-sided connector.
  leavitt-crossed-gram-pauli-charge-has-sectorwise-escape: that constructs the label-plus-gauge cancellation before a selector connector is added; this shows that finite reflection actors can be restored by orbit induction and therefore do not remove the fixed-depth escape.
---

# Odd Leavitt reflection words retain an exact stationary XOR overlap sector

**ESTABLISHED.**  Let `p` be odd.  For orthogonal Leavitt prefix idempotents
`P,E` and `Q=P+E`, the literal units

```text
r_P=1-2P,       r_E=1-2E,       r_Q=1-2Q               (OLX1)
```

are involutions and satisfy

```text
[r_P,r_E]=1,                 r_Q=r_P r_E.               (OLX2)
```

The signed one-sided connector from
`odd-leavitt-steinberg-reflection-prerequisites` gives, after choosing the
transported Steinberg lift,

```text
u r_Q u^(-1)=r_P.                                      (OLX3)
```

Equations `(OLX2)--(OLX3)` do **not** imply that the negative projections
of `r_P,r_E` are orthogonal.  They have the following exact finite canonical-
trace model.  In

```text
K=(C_2)^2 semidirect GL_2(F_2) ~= S_4,                  (OLX4)
```

write the normal Klein four group as `{1,d,e,de}` and choose the involutive
transvection `u` with

```text
u d u^(-1)=de,              u e u^(-1)=e.               (OLX5)
```

Then `u(de)u^(-1)=d`, so `(r_P,r_E,r_Q,u)=(d,e,de,u)`
satisfies every relation `(OLX2)--(OLX3)`.  In the regular representation of
`K`, all three reflection words have trace zero.  Nevertheless, for

```text
P'=(1-d)/2,              E'=(1-e)/2,
Q'=(1-de)/2,                                             (OLX6)
```

one has

```text
tau(P')=tau(E')=tau(Q')=1/2,       tau(P'E')=1/4.        (OLX7)
```

Thus the connector defect is zero while the proposed paid complement has
mass `1/2`.  The hypothesis `P'<=Q'` needed by the sharp one-sided trace
ledger is false: `(OLX2)` remembers symmetric difference,

```text
Q'=P'+E'-2P'E',                                         (OLX8)
```

not orthogonal union.

This escape scales through every finite prefix depth.  Put independent fair
bits on the leaves of a finite binary tree and define each prefix reflection
to be the parity of the bits below it.  Every nonzero prefix parity is
balanced, every parent is the XOR of its two children, and sibling negative
cuts overlap with trace `1/4`.  Any finite family of prefix-parity changes of
coordinates is implemented by Koopman unitaries for the corresponding
finite linear group.  In particular sibling symmetry and the parent-to-child
transvection do not remove the stationary sector.

The full fixed-depth crossed-Pauli cell also retains the escape.  On each
joint selector sector use the exact sectorwise Clifford construction of
`leavitt-crossed-gram-pauli-charge-has-sectorwise-escape`: an inverse gauge
Weyl pair on the overlap cancels the label Weyl commutator, while the
diagonal/common-`p` phase cells are left unchanged.  To add a finite actor,
take the direct sum over its finite orbit of selector sectors and let the
actor permute the summands and the private gauge factors.  This is exact,
finite-dimensional, and preserves all reflection, finite covariance, and
crossed-Pauli relations in that cell.  It costs additional multiplicity but
no defect.  Hence a fixed-depth reflection-controlled Pauli packet cannot
exclude the overlap by a dimension-independent HS estimate.

Odd characteristic therefore removes the **literal wordization** problem
but not the root-to-coefficient/support decoder.  The common order-`p`
Heisenberg word and its finite-dimensional annihilation theorem remain
valid, but the reflection words do not connect its visibility to projection
inclusion.  A successful use of odd characteristic must add a relation that
detects the product `P'E'` itself (or an unbounded coherent incidence which
prevents the private-gauge orbit induction), rather than another reflection
or finite connector covariance row.

