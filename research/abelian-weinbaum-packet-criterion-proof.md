---
rg: 2
id: abelian-weinbaum-packet-criterion-proof
kind: route
title: Quotient by the saturated relator line and avoid finitely many lattice hyperplanes
target: abelian-weinbaum-packet-criterion
requires: []
artifacts:
  - research/artifacts/one-relator-weinbaum-gate-and-berlai-calibration-2026-08-30.md
---

Let `A=Z^d/L`.  Saturation makes `A` free abelian, and the image of `e(v)` in
`A` is zero.  Hence the abelianization map `F->A` factors through
`F/<<v^m>>` for every `m`.  A subword `u` has nonzero image precisely when
`e(u) notin L`.  This proves (2) gives a packet-retaining torsion-free abelian
quotient.

If (1) holds, the map factors through the torsion-free abelianization of
`F/<<v^m>>`.  In a torsion-free abelian target the relation `m e(v)=0` forces
`e(v)=0`, so the map kills `L`.  Therefore `e(u) in L` would force the image
of `u` to vanish.  This proves (1) implies (2).

It remains to improve `A` to one cyclic quotient.  Under (2), the packet gives
finitely many nonzero vectors `a_1,...,a_k in A`.  In the dual lattice
`Hom(A,Z)`, each equation `lambda(a_i)=0` cuts out a proper sublattice lying
in a rational hyperplane.  A finite union of proper rational hyperplanes does
not cover the lattice, so choose `lambda:A->Z` outside their union.  The
composition `F/<<v^m>> -> A -> Z` is nonzero on every packet element.  This
proves (3), and (3) trivially implies (1).
