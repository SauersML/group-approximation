---
rg: 2
id: leavitt-crossed-gram-pauli-sector-escape-proof
kind: route
title: Cancel the overlap Pauli phase with a multiplicity Pauli phase
target: leavitt-crossed-gram-pauli-charge-has-sectorwise-escape
requires: []
---

# Cancel the overlap Pauli phase with a multiplicity Pauli phase

Decompose over the four joint selector projections.  The controlled label
gates commute on three sectors and anticommute on `F_0F_1`, proving `(LPG2)`.
For a common irreducible packet, Schur's lemma leaves one external
commutator `K`; expanding its trace against `1-2F` proves `(LPG2b)`.
In `(LPG3)`, tensor a second anticommuting Pauli pair only on that fourth
sector.  Multiplication of the two central commutator signs gives `+I`,
while the overlap projection still has trace `1/4`.  This proves the finite
exact typed-sector escape and isolates a common sector-connecting packet as
the sole extra datum needed by the positive identity.
