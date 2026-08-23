---
rg: 2
id: fixed-pi-from-one-common-pauli-intertwiner
kind: route
title: Telescope one common four-Pauli intertwiner through s4
target: fixed-pi-degree-fingerprints-packet-label-factor
requires:
  - four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap
  - one-common-intertwiner-carries-the-four-pauli-pi-bridge
---

Use packet degree `r=2`.  The common-intertwiner claim supplies the same
positive carrier, one degree-two source algebra, and the fixed two-qubit
target tuple.  By Amitsur--Levitzki the source `s4` value is zero.  Repeatedly
replace `D_jT` by `TC_j` in each of the 24 monomials to obtain `(CPI2)`.
The four-Pauli estimate gives the fixed lower bound on the target value, and
the full-support estimates on `T` prevent that value from disappearing after
right multiplication by `T`.  This is precisely clauses 1--3 of the fixed-PI
claim for one fixed degree.

The route uses neither scalar joint fullness nor spectator elimination.
`separate-pauli-branch-transports-do-not-carry-s4` proves that replacing the
one common `T` by the two native branch conjugators invalidates the argument
even at zero defect.
