---
rg: 2
id: arithmetic-star-packet-non-mf-proof
kind: route
title: Attach S9 to the eight compression cosets and apply finite-packet collapse
target: arithmetic-star-packet-non-mf
requires:
  - arithmetic-star-packet-carrier
  - finite-noncommutative-packet-compression-collapse
artifacts:
  - notes/FINITE_PACKET_SELF_COPY_COLLAPSE.md
  - GroupApproximation/Sofic/LiteralAffineCongruenceSource.lean
  - GroupApproximation/Sofic/LiteralAffineCongruenceKazhdan.lean
  - GroupApproximation/Sofic/LiteralAffineCongruenceTorsionFree.lean
---

The carrier theorem supplies the finitely presented amalgam, its embedded
finite packet, the compressed-subgroup fixedness, and the nontrivial marked
commutator.  Apply finite-packet compression collapse to kill that mark in
every norm matrix corona.  A faithful norm-corona embedding would preserve
it, so none exists.
