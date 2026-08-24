---
rg: 2
id: finite-group-corona-tail-exactification-proof
kind: route
title: Exactify the coordinate tables and recover the corona class
target: finite-group-corona-tail-exactification
requires:
  - finite-group-opnorm-support-profile
artifacts:
  - notes/FINITE_PACKET_SELF_COPY_COLLAPSE.md
---

Choose unitary coordinate lifts of the finitely many elements of `F`.  Their
multiplication-table defects converge to zero in operator norm because the
given map is a homomorphism in the corona.  Apply
`finite-group-opnorm-support-profile` to this fixed table at every sufficiently
late coordinate.  It gives an exact representation in the same matrix
dimension whose operator-norm distance from the chosen lifts tends to zero;
hence the corrected sequence has the same corona class.  This proves the
tail exactification without introducing a second finite-group stability
primitive in the graph.

Equivalently, `C*(F)` is finite-dimensional and semiprojective.  Choose lifts
of the finitely many matrix units in
`C*(F)=direct_sum_j M_(r_j)`.  Their defects are `c_0`; spectral rounding of
the diagonal idempotents and polar correction of the off-diagonal partial
isometries give exact matrix units with correction tending to zero.  This is
an independent C-star proof of the same corollary, not a separate Cairn
dependency.
