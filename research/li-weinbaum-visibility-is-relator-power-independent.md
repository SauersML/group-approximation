---
rg: 2
id: li-weinbaum-visibility-is-relator-power-independent
kind: claim
title: Locally indicable visibility of a one-relator packet is independent of the relator exponent
distinct_from:
  one-relator-weinbaum-packet-amenably-visible: that is the open universal existence statement; this proves that its torsion presentations give exactly the same homomorphisms to locally indicable targets as the corresponding primitive-relator presentation.
  one-relator-groups-sofic: that asks for finite approximations for all one-relator groups and includes the torsion case already settled by other methods; this is an exact factorization theorem showing that torsion supplies no additional locally indicable quotient for the Weinbaum gate.
artifacts:
  - research/artifacts/one-relator-weinbaum-gate-and-berlai-calibration-2026-08-30.md
---

Let `F` be a group, let `v in F`, and put

    G_m=F/<<v^m>>,       G_1=F/<<v>>,       m>=1.

For every locally indicable group `Q`, precomposition with the natural quotient
`p_m:G_m->G_1` is a bijection

    Hom(G_1,Q) -> Hom(G_m,Q).

Consequently, for any fixed finite packet of words in `F` (in particular the
proper nonempty contiguous subwords of `v`), there is a homomorphism from
`G_m` to an amenable locally indicable group that is nontrivial on the packet
if and only if there is one from `G_1`.

Thus the torsion case `m>1` and the torsion-free primitive-relator case `m=1`
of the Weinbaum visibility gate are not merely analogous: they are the same
exact quotient problem.
