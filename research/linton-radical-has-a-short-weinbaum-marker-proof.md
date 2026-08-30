---
rg: 2
id: linton-radical-has-a-short-weinbaum-marker-proof
kind: route
title: Force a proper subword to die or make the rationally perfect kernel free
target: linton-radical-has-a-short-weinbaum-marker
requires: [linton-rational-derived-series-theorem]
artifacts:
  - research/artifacts/one-relator-weinbaum-gate-and-berlai-calibration-2026-08-30.md
---

Linton's theorem makes `H` residually rationally solvable and `R` rationally
perfect.  A residually rationally solvable group is locally indicable: for a
nontrivial finitely generated subgroup `L<=H`, choose the first rational
derived layer containing `L` whose successor does not contain it.  Restriction
to that layer's torsion-free abelian quotient gives a nonzero map from `L` to a
finitely generated torsion-free abelian group, and hence an epimorphism to
`Z`.

Suppose every proper nonempty subword of `w` survived under `pi`.  Apply
Linton, arXiv:2407.09272v2, Theorem 3.2, with exponent `m=1` and target `H`.
It decomposes `ker(pi)=R` as a free product of a free group and subgroups of
the free factors `A,B`.  Nielsen--Schreier therefore makes `R` free.

But a nontrivial free group has nonzero torsion-free abelianization and cannot
be rationally perfect.  Hence `R=1`, contrary to the hypothesis.  Some proper
subword `u` must therefore die in `H`.  Weinbaum's theorem says that every
proper nonempty subword of the one-relator word is nontrivial in `G`, so this
`u` lies in `R\{1}`.

Linton's Corollary 1.4 computes the canonical word defining `H`; testing the
finite list of proper subwords with the one-relator word problem finds `u`.
If `k=1`, the established computation `R_ab=(Z/kZ)[H]` gives `R=R'`, proving
the final assertion.
