---
rg: 2
id: sparse-three-site-fourth-moment-proof
kind: route
title: Count balanced incidences and evaluate the Pauli anchor grading
target: three-site-pauli-refutes-unpeeled-fourth-moment
requires:
  - quadratic-redundant-check-overlay-gives-uniform-face-gap
---

Bounded column degree leaves only constantly many bad original rows.  The
balanced repeated-original layer turns each into `Theta(M)` bad copies, and
all pair sums involving that constant bad set contribute another `O(M)`;
the denominator is `Theta(M^2)`.  Equality copies agree exactly.  Direct
Pauli multiplication proves `(STP2)` and the four ordered noncommuting
pairs give `(STP5)`.  The chosen exact row occurs `Theta(M)` times, and on
anchor `k` its `(i,j)` two-odd-factor product is the identity, proving
`(STP4)`.
