---
rg: 2
id: split-higman-cycle-has-haar-marginals-and-maximal-role-gap
kind: claim
title: Split Higman doubling edges have Haar marginals and a maximal role gap
distinct_from:
  periodic-bs-clock-defeats-spectral-first-hit-checksum: that audits one Baumslag--Solitar edge; this identifies exactly what is missing when four such edges are cyclically glued.
  finite-selector-gadget-induction-barrier: that concerns which abelian characters extend to finite-group representations; this concerns equality of two noncommuting operator roles with identical limiting marginal laws.
---

Consider the cyclic doubling equations

```text
g_i g_(i+1) g_i^(-1)=g_(i+1)^2,        i in Z/4Z.     (SHC1)
```

Before identifying the two occurrences of each `g_i`, every edge has an
exact `q`-dimensional model: assign the conjugator occurrence the periodic
matrix `P_q` and the target occurrence `Z_q` from
`periodic-bs-clock-defeats-spectral-first-hit-checksum`.  All four equations
then hold exactly.

For primes `q_n->infinity` chosen there, every one of the eight occurrence
unitaries has Haar limiting marginal moments.  Nevertheless the incoming
target occurrence and outgoing conjugator occurrence of the same cyclic
generator satisfy

```text
||P_(q_n)-Z_(q_n)||_2^2=2-2/q_n->2.                  (SHC2)
```

Therefore no argument can close the Higman cycle using only the four local
doubling defects and equality of the individual spectral measures or power
moments assigned to repeated generator roles.  Those data admit exact split
edge models with asymptotically maximal occurrence inconsistency.

This is not a finite-dimensional approximate representation of the glued
Higman group: the missing equalities between occurrences are precisely the
load-bearing relations.  It is a sharp interface countermodel.  Any Higman
square-function checksum must extract a joint four-edge eigenbasis holonomy,
a common coupling of the repeated occurrences, or another matrix-coordinate
quantity that pays for `(SHC2)`.  A scalar spectral first-hit ledger cannot
do so.

