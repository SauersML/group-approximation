---
rg: 2
id: modular-one-sided-inverse-has-no-clifford-phase-lift
kind: claim
title: Clifford phases cannot lift a modular one-sided inverse into a complex group algebra
distinct_from:
  atlas-a4-four-cycle-dirichlet-ceiling: that gives one explicit three-term norm witness inside the A4 atlas; this is a general cyclotomic reduction theorem for every group and every finite-support modular one-sided inverse.
  direct-finiteness-not-inherited-by-quotients: that explains why a quotient of a directly finite ring may fail direct finiteness; this proves that a phase-decorated section of a modular one-sided inverse cannot exist in a complex group algebra.
  leavitt-unit-group-algebra-not-directly-finite: that is the open existence of a one-sided inverse in the binary Leavitt unit group algebra; this is a conditional obstruction to transporting any such witness through Pauli or Clifford phases.
artifacts:
  - research/artifacts/two-primary-phase-lift-obstruction-2026-08-21.md
---

Let `G` be any group and let

```text
a=sum_(g in S) g,       b=sum_(h in T) h       in F_2[G]
```

have finite supports and satisfy `ab=1` but `ba!=1`.  Fix `m>=1`.  There are
no coefficient functions

```text
alpha:S->mu_(2^m),      beta:T->mu_(2^m)
```

for which the phase-decorated complex group-algebra elements

```text
A=sum_(g in S) alpha(g)g,   B=sum_(h in T) beta(h)h
```

satisfy `AB=1` in `C[G]`.

Consequently a Pauli/Clifford phase layer cannot turn a characteristic-two
one-sided inverse into a complex one while assigning one scalar phase to
each support term.  For fixed `m,S,T` there is moreover a positive uniform
regular-trace `L2` gap from `AB=1`, so the obstruction survives regular-trace
hyperlinear microstates.
