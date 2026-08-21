---
rg: 2
id: canonical-trace-tests-robustify-pauli-quarter-holonomy
kind: claim
title: A fixed finite trace window robustifies the Pauli quarter-carrier holonomy
requires:
  - two-pauli-quarter-carriers-have-fixed-reflection-holonomy
  - trace-conditioned-kleene-microstate-diagonal
distinct_from:
  fixed-holonomy-on-overlap-pays-relator-energy: that starts from legal word-level reflections on an aligned finite packet; this proves the scalar projection-polynomial floor before the Hecke reflections are groupified.
  trace-functorial-bcs-signal-groupification-impossible: that rules out an exact decoder on every tracial representation; this uses only finitely many canonical group-trace targets in the diagonal search.
---

Let `P,Q` be orthogonal projections in a finite tracial algebra and put

```text
R=2P-1,       S=2Q-1.
```

Then

```text
||RSRS-1||_2^2
 =||RS-SR||_2^2
 =16||PQ-QP||_2^2
 =32(tau(PQ)-tau(PQPQ)).                              (CTH1)
```

The last identity follows by expanding

```text
||PQ-QP||_2^2
 =tau(QPQP)+tau(PQPQ)-tau(QPQ)-tau(PQP)
 =2tau(PQ)-2tau(PQPQ).
```

For the two exact atlas quarter carriers, the finite trace targets are

```text
tau(PQ)=1/16,       tau(PQPQ)=3/64,                   (CTH2)
```

so `(CTH1)` equals `1/2`.

All ingredients are fixed finite polynomials in the named atlas packet
unitaries.  Exactify the fixed involution packets and replace the resulting
almost projections by their spectral projections.  Word telescoping,
finite-group flexible stability, and Cauchy--Schwarz give a computable fixed
constant `C` such that any matrix tuple passing the finite trace tests for
the words occurring in `(CTH2)` obeys

```text
||R(U)S(U)R(U)S(U)-1||_2^2
 >=1/2-C(def(U)+sep_F(U)).                             (CTH3)
```

Here `F` is one fixed finite word window, and no constant depends on matrix
dimension.  The exact numerical value of `C` is immaterial for the
trace-conditioned diagonal: the defect and separation terms tend to zero
before the fixed `1/2` floor is used.

This closes the analytic robustness of the holonomy.  It deliberately does
not claim that `R,S` are words of the original group.  The remaining finite
compiler interface is algebraic: realize the two Boolean projection
reflections as balanced derived-packet selector words with a common robust
conjugation table, and connect their commutator to the intended return
relation.  Once that interface is supplied, `(CTH3)` is already the required
dimension-independent normalized-HS floor.
