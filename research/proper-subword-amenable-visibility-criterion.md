---
rg: 2
id: proper-subword-amenable-visibility-criterion
kind: claim
title: One amenable quotient retaining the finite Weinbaum packet makes a one-relator group sofic
distinct_from:
  residually-rationally-solvable-one-relator-sofic: that assumes every nontrivial element survives in some rationally solvable quotient; this needs only one amenable locally indicable quotient retaining the finitely many proper subwords of one fixed relator, and that quotient need not be solvable.
  linton-radical-sofic: that asks for soficity of the full canonical radical; this criterion neither assumes nor concludes that the radical is sofic, because it replaces the canonical quotient by one packet-separating amenable quotient whose kernel is forced to have a free-product decomposition.
  one-relator-fox-magnus-descent-to-derived-linton-radical: that constructs a canonical finite-lamp quotient with kernel `R'`; this is a conditional theorem for an arbitrary amenable locally indicable quotient and uses proper-subword visibility to make its kernel a free product.
artifacts:
  - research/artifacts/one-relator-weinbaum-gate-and-berlai-calibration-2026-08-30.md
---

Let `F=A*B` be a finite-rank free group split into two nontrivial free factors,
let `v` be cyclically reduced of free-product syllable length at least two and
not a proper power, and let

    G = F/<<v^m>>,             m >= 1.

Fix the cyclic spelling of `v`, and let `S(v)` be the finite set of elements
represented by its proper nonempty contiguous subwords.  If there is a
homomorphism

    phi : G -> Q

to an amenable locally indicable group such that `phi(s) != 1` for every
`s in S(v)`, then `G` is sofic.

Only this one finite presentation-defined packet must survive.  The hypothesis
is strictly local and does not assume that `G` is residually amenable.
