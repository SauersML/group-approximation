---
rg: 2
id: separate-occurrence-pauli-gauge-countermodel-proof
kind: route
title: Conjugate the two Pauli actors into one commuting occurrence frame separately
target: separate-occurrence-arrows-do-not-lock-pauli-gauge
requires:
  - controlled-pauli-commutator-is-and-times-multiplicity-commutator
---

Work first on the active carrier `L tensor G`. The Pauli and Hadamard
relations give

```text
X_g Z_g=-Z_g X_g,               H_g X_g H_g=Z_g.       (SAP1)
```

Consequently the two equalities in `(SAF3)` hold before compression:

```text
W_A A_11 W_A^*
 =(I_L tensor H_g)(I_L tensor X_g)(I_L tensor H_g)
 =I_L tensor Z_g=A^o,

W_B B_11 W_B^*
 =I_L tensor Z_g=B^o.                                  (SAP2)
```

The targets are equal, hence commute. Taking `R=E_11` proves every
left-compressed equality in `(SAF3)`, and

```text
tau(R)=tau(E_11).                                       (SAP3)
```

Thus the mass inequality in `(AIM1)` holds with `c=1`, `C=0`, while
`(AIM2)` has zero defect.

On the other hand, the commutator convention for involutions gives

```text
[A_11,B_11]
 =I_L tensor (X_g Z_g X_g Z_g)
 =-I_(L tensor G).                                      (SAP4)
```

In normalized Hilbert--Schmidt norm on the active carrier,

```text
||[A_11,B_11]-1||_2^2=4.                               (SAP5)
```

There is no selector transport hidden here. In a four-sector direct sum,
take `W_A` to act by `I_L tensor H_g` on `E_11` and by the identity on
the other sectors; take `W_B=I`. Both arrows commute with every selector
projection, so `W_A R W_A^*=W_B R W_B^*=R`.

The example is finite-packet exact. The one-qubit Clifford group generated
by `X_g,Z_g,H_g` is finite up to its finite scalar center, and adjoining
the selector projections as spectral projections of commuting finite-order
signs keeps the generated matrix group finite. Passing to a regular
representation, if desired, preserves all displayed equalities and gives
the marked active atom positive Plancherel mass.

The logical failure is independent conjugation. From

```text
A^o=W_A A_11 W_A^*,          B^o=W_B B_11 W_B^*
```

and `[A^o,B^o]=1`, one obtains a relation between `A_11` and the
conjugate of `B_11` by the relative frame `W_A^*W_B`, not a relation
between `A_11` and `B_11`. In this example that relative frame is exactly
the Hadamard which rotates one Pauli axis into the other.

A common arrow `W_A=W_B` would remove this countermodel: conjugating
`[A^o,B^o]=1` back by that arrow gives `[A_11,B_11]=1`. More generally
one needs a mixed relation which makes the relative frame invisible to both
actors on `R`. This additional joint-frame statement, rather than the two
separate estimates in `(AIM1)`, is the revised minimal gate.
