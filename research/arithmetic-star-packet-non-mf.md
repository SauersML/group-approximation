---
rg: 2
id: arithmetic-star-packet-non-mf
kind: claim
title: The affine self-compressor with one finite star-transposition packet is finitely presented and non-MF
distinct_from:
  commuting-lamp-quotient-not-mf: That construction uses a pairwise commuting involution orbit; the star transpositions here do not commute.
  kazhdan-clifford-non-mf-construction: That construction uses a central Clifford sign; the finite packet here is `S_9`, which has trivial center.
  normal-kazhdan-defect-non-mf: That detector kills a normal Kazhdan subgroup inside the compression defect; this route kills one noncommuting packet commutator by multiplicity rank.
artifacts:
  - notes/FINITE_PACKET_SELF_COPY_COLLAPSE.md
  - GroupApproximation/Sofic/LiteralAffineCongruenceSource.lean
  - GroupApproximation/Sofic/LiteralAffineCongruenceKazhdan.lean
  - GroupApproximation/Sofic/LiteralAffineCongruenceTorsionFree.lean
---

Use the finitely presented group `W` and nontrivial mark `w=[p_0,k]` supplied
by `arithmetic-star-packet-carrier`.  Its finite packet `F=S_9` is normalized
by `P`, while the compressed subgroup fixes `k`, so
`finite-noncommutative-packet-compression-collapse` makes every norm-corona
representation kill `w`.  Therefore `W` is not operator-MF.

**FORMALIZATION STATUS.**  Cairn's affine source inputs are kernel-checked in
the linked modules.  The `S_9` semidirect packet, amalgam carrier, and
application of the paper-level packet-collapse theorem remain outside the
Lean kernel.
