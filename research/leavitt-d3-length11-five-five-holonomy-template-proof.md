---
rg: 2
id: leavitt-d3-length11-five-five-holonomy-template-proof
kind: route
title: Cancel four pivot copies locally and retain the four holonomy arcs
target: leavitt-d3-length11-five-five-holonomy-template
requires:
  - leavitt-minimal-cycle-is-hnn-holonomy
  - leavitt-d3-length9-compound-holonomy-is-absent
---

The exponent-three length-eleven sign paths split by sorted stable-letter
valence as follows:

```text
(3,3,5): 165,       (1,3,7): 88,
(1,5,5):  66,       (1,1,9): 11.
```

The apparent two-unary continuation `(1,1,9)` has the same copy-index defect
as length nine.  For the representative signs
`(-,+,-,+,-,+,-,+,+,+,+)`, its two unary corners have reduced index words

```text
(0,1,0,1,0,1,0,1,0,1,2),
(0,1,2,1,2,1,2,1,2,1,2).
```

They differ at the third syllable, so no all-nonidentity compound packet can
make the second unary relation the source identity.

The `(1,5,5)` profile survives.  A representative is

```text
(-,-,+,-,+,+,-,+,+,+,+),
```

and both residual orbits have stable signs `(-,+,-,+,+)` after cyclic
rotation.  If their corners are `C1,...,C5`, substituting `z=H^(-1)` gives

```text
H C1 H^(-1) C2 H C3 H^(-1) C4 H^(-1) C5.           (F51)
```

Put

```text
C1=H^(-1),   C2=H X,   C3=H^(-1) A,
C4=H Y,      C5=H B.                                  (F52)
```

Successive free reductions in `(F51)` give

```text
1 * X * A * Y * B = X A Y B.
```

Apply `(F52)` to the second residual orbit with the same `H,X,Y` and replace
`A,B` by `C,D`.  The two relators are precisely the same-orientation minimal
cycle classified in `leavitt-minimal-cycle-is-hnn-holonomy`, so eliminating
`X` gives

```text
Y^(-1)(A^(-1)C)Y=B D^(-1).
```

This proves abstract cyclic compatibility at the signed-corner level.  The
remaining realization problem is narrower: assign eleven actual compound
coefficient slots so that the ten corner equalities `(F52)` hold in the free
product of the three Leavitt coefficient copies.  No packet enumeration is
part of this theorem.
