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

Take Cairn's level-three affine Kazhdan source
`P=Gamma(3) ltimes Z^3` with the certified translation-doubling embedding
`alpha`, whose image `H=alpha(P)` has index `8`.  Let `E` be the ascending HNN
extension with `tPt^(-1)=H`.  On the eight left cosets `X=P/H`, let
`F=Sym(X disjoint_union {star})=S_9`, with `P` acting by left translation on
`X` and fixing `star`.  Put `A=F rtimes P`, let `k=(H star)`, and form
`W=A *_P E`.

The subgroup `H` fixes `k`, while the certified omitted element `p_0 notin H`
moves it.  Hence `w=[p_0,k]` is nontrivial in `A` and remains nontrivial in the
amalgam.  The finite packet `F` is normalized by `P`, so
`finite-noncommutative-packet-compression-collapse` makes every norm-corona
representation kill `w`.  Therefore `W` is not operator-MF.  Since `P` and
both factors are finitely presented and the amalgamated subgroup `P` is
finitely generated, `W` is finitely presented.

**FORMALIZATION STATUS.**  Cairn's affine source inputs are kernel-checked in
the linked modules.  The `S_9` semidirect packet, amalgam carrier, and
application of the paper-level packet-collapse theorem remain outside the
Lean kernel.
