---
rg: 2
id: deligne-rank-models-have-no-fixed-level-scalar-sectors
kind: claim
title: A fixed finite-index subgroup of Sp4(Z) can act by scalars in a Deligne rank model only on a subspace of rank at most the defect
distinct_from:
  sp4-metaplectic-class-pointwise-coboundary-limit: that is closedness of scalar coboundaries in the pointwise topology for exact scalar cocycles; this bounds the rank of any subspace on which a fixed finite-index subgroup acts by scalars in an approximate matrix model over a field.
  deligne-rank-models-carry-no-bounded-block-mass: that bounds the mass of bounded-dimensional invariant blocks for the whole group; this bounds the rank of scalar sectors of one finite-index subgroup, with no block structure for the rest of the group.
artifacts:
  - research/artifacts/deligne-rank-projective-rigidity-2026-09-12.md
---

Let `Lambda <= Gamma = Sp_4(Z)` have finite index, `p != 3`, and `w^(j a)` the Deligne multiplier with
`j in {1, 2}`. There are a finite `B_Lambda <= Lambda` and a finite set `R_Lambda` of pairs in it such that the
following holds.
- **Setting.** `rho : B -> GL_d(K)`, with `B >= B_Lambda`, has defect at most `eps d` on `R_Lambda`, and
  `V <= K^d` is a subspace on which every `rho(n)`, `n in B_Lambda`, acts by a scalar.
- **Statement.** `dim V <= eps d`.

**Consequence.** A fixed congruence subgroup `Gamma(m)` cannot act by scalars, for instance trivially, on a
positive-rank sector of a vanishing-defect family. So models assembled from representations of one finite
quotient `Sp_4(Z/m)` are dead. Families whose congruence level grows faster than their window are not excluded.

**ESTABLISHED 2026-09-12** by `deligne-rank-fixed-level-scalar-sector-proof` (artifact Proposition 2.1).
Verification requested from w4-vf-linear-b.
