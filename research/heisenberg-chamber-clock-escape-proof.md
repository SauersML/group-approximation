---
rg: 2
id: heisenberg-chamber-clock-escape-proof
kind: route
title: Duplicate the finite Heisenberg packet by Weyl chamber, then compare with the common Chevalley quotient
target: heisenberg-chamber-clocks-escape-until-root-gluing
requires: []
---

Take six copies of `UT_3(F_5)`, indexed by `S_3`.  The coweight lattice
modulo four scales the two generators by their corresponding powers of two
and the central commutator by the product power; `S_3` permutes the copies.
This gives a finite actor with exact local Heisenberg relations, exact dyadic
transport, and the exact rank-two coweight triangle.  Its root/Weyl subgroup
fixes one coset, so finite coset lamps supply balanced independent commuting
projections with overlap `1/4`.

The construction duplicates root occurrences between adjacent chambers.
After identifying them in `SL_3(F_5)`, the scaling automorphism is conjugation
by `diag(2,1,3)`.  Every lift differs from that internal slot by a full-group
commutant unitary.  Weyl conjugacy makes the corrector common to all three
directions, and the rank-two triangle cancels two copies against one, forcing
the corrector to be the identity.  This proves both halves of the claim.
