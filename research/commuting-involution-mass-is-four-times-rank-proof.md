---
rg: 2
id: commuting-involution-mass-is-four-times-rank-proof
kind: route
title: Read the mass off the Gram trace, and the rank off the half-square projection
target: commuting-involution-mass-is-four-times-rank
requires: []
artifacts:
  - GroupApproximation/Sofic/InvolutionRankMass.lean
---

## Why sufficient

Machine-checked, no `sorry`, no axiom, no literature premise.  Dossier
3.1--3.3.

**Mass is a trace.**  `matMass_eq_re_trace_conjTranspose_mul`: the unnormalized
Frobenius mass of `X` is `Re tr(X^H X)`, by summing `normSq` entrywise.

**The cubic identity.**  For commuting exact involutions,
`conjTranspose_sub_eq` gives self-adjointness of `T = u - w`;
`sub_mul_sub_of_commute`, `sub_mul_mul_eq_neg_sub` and `sub_mul_sub_mul_sub`
give `T^3 = 4T` by expanding with `u^2 = w^2 = 1` and `uw = wu`.

**The half-square projection.**  `halfSqProjection` is `T^2/4`;
`halfSqProjection_isOrthogonalProjection` checks idempotence and
self-adjointness from the cubic identity, and `sub_mul_halfSqProjection` records
`T . (T^2/4) = T`.

**The identity.**  `re_trace_eq_rank_of_isOrthogonalProjection` — an orthogonal
projection's trace is its rank — combined with the trace formula gives
`matMass_sub_eq_four_mul_rank`, via `rank_halfSqProjection`.

**Triangle inequality.**  `rank_add_le` then `rank_sub_le_add`, by writing
`a - c = (a - b) + (b - c)`.

**Projection rigidity.**  `rank_le_of_norm_sub_lt_one` and
`rank_eq_of_projections_close`: if `‖p - q‖_op < 1` then `p` restricted to the
range of `q` is injective, so the ranks compare both ways, hence are equal.

**The reverse bound.**  `matMass_le_rank_mul_sq_opNorm`: sum the eigenvalues of
the Gram matrix `X^H X` over an eigenbasis; each is at most `‖X‖_op^2`, and the
number of nonzero ones is `rank X`.

## Scope, stated honestly

The exact identity holds only on the commuting-**involution** locus (`m = 2`),
and the file says so in its name.  For higher torsion the corresponding
statement is the general inequality `‖X‖_F^2 <= rank X . ‖X‖_op^2` above, with
the constant no longer sharp; nothing here claims otherwise, and no result in
this route is used at `m > 2`.
