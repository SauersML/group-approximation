---
rg: 2
id: rational-solvable-weinbaum-visibility-boundary
kind: claim
title: The Linton radical is the exact boundary for rational-solvable visibility of a finite packet
distinct_from:
  rational-perfect-core-blocks-rrs-kernel-lifts: that obstructs exact lifts over the canonical Linton quotient when the added kernel is residually rationally solvable; this gives an if-and-only-if for arbitrary rationally solvable quotient maps, with no prescribed map to the canonical quotient.
  linton-radical-has-a-short-weinbaum-marker: that proves some proper relator subword lies in every nontrivial torsion-free Linton radical; this characterizes exactly which finite packets can be retained by one rationally solvable quotient and turns that marker into a sharp no-go theorem.
  residually-rationally-solvable-one-relator-sofic: that concludes soficity from a global residual hypothesis; this constructs one amenable locally indicable quotient retaining any prescribed finite subset disjoint from the rational residual.
artifacts:
  - research/artifacts/one-relator-weinbaum-gate-and-berlai-calibration-2026-08-30.md
---

Let `G` be any group and let

    R=G_Q^(omega)=intersection_(n>=0) G_Q^(n)

be the intersection of its rational derived series.  For a finite subset
`S subset G\{1}`, the following are equivalent:

1. `S intersect R` is empty;
2. some homomorphism from `G` to a rationally solvable group is nontrivial on
   every element of `S`;
3. some homomorphism from `G` to an amenable locally indicable group which is
   rationally solvable is nontrivial on every element of `S`.

When `G=F/<<v>>` is a torsion-free one-relator group and `S` is its full
Weinbaum packet, [[linton-radical-has-a-short-weinbaum-marker]] implies that
these conditions hold if and only if `R=1`.  Therefore every solution of the
open packet gate in the nontrivial-radical case must have amenable image
**outside the rationally solvable class**.  If `R` is perfect, as in the
Baumslag--Gersten and Berlai `k=l+1` families, that image must in fact be
nonsolvable.  Rational-solvable and finite-stage Fox--Magnus constructions
cannot solve the general hard case.
