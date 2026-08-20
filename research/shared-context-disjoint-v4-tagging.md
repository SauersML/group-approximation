---
rg: 2
id: shared-context-disjoint-v4-tagging
kind: claim
title: Give repeated V4 failure atoms pairwise disjoint tags from the shared BCS tuple
distinct_from:
  shared-context-exclusive-v4-tagging: that must additionally exclude every source tag type from the complement of the forbidden parent; this drops that condition by using constant repetition and ambient capacity.
  disjoint-tag-covariance-controls-cross-gram: that proves the analytic estimate for supplied tags; this must construct their source/target representations and covariance maps from group data.
---

For the constant repetition count chosen in `(CRV4)`, construct one finitely
presented marked extension and a decoder for every sufficiently accurate
finite-dimensional marked microstate which supplies:

1. a fixed finite tag group `H`;
2. pairwise disjoint source tag representations `pi_i`, one for each radical-
   atom occurrence in the repeated synchronized V4 failures;
3. one target representation `rho` of `H` on a common fixed matrix
   amplification;
4. partial isometries `T_i` with source projections equal to those failure
   atoms; and
5. a bounded-overlap covariance estimate

   ```text
   sum_(i,s)||rho(s)T_i-T_i pi_i(s)||_2^2
      <= C E_rel+o(1).                                  (SCD1)
   ```

Only pairwise disjointness `Hom_H(pi_j,pi_i)=0` for `i!=j` is required. No
tag type must be absent outside a nonlinear parent projection.

The tags must still be extracted jointly before the repeated context copies
are separated, and the exact non-CE tracial BCS representation must extend.
An ordinary finite graph-of-groups atlas cannot solve this: its regular
stationary representation supplies all compatible tag types and absorbs the
apparent branching. The required decoder must use shared-context operator
data, a property-`(T)` coefficient wall, or another finite-dimensional-only
selection mechanism.

The matrix-only qualifier is forced by
`repeated-v4-tags-cannot-be-universal-word-branches`.  After enlarging the
already fixed repetition count, any fixed family of exact word branches
would also exist in the canonical left regular representation, whose positive
regular forbidden mass would violate ambient capacity.  Hence a successful
decoder must select its tag types or polar branches from finite multiplicity
data; it cannot merely reveal universal branches that were present all along.

## Attempts

- **Parent exclusivity. Unnecessary.**
  `constant-repetition-v4-needs-only-disjoint-tags` replaces it by a fixed
  number of duplicate batches and the ambient identity capacity.
- **Independent context tags. Dead.** They do not arise from a common target
  representation and do not constrain cross-Gram products.
- **Universal word branches. Impossible.** The canonical group trace has
  positive regular V4 failure mass.  Exact disjoint word branches repeated
  beyond its reciprocal violate capacity inside the group factor itself.
- **Fixed HNN character atlas. Dead.** The regular stationary type flow
  absorbs every finite list of subgroup character identifications.
- **Dummy affine clocks do not remove the repetition bottleneck.**
  `affine-source-charts-have-a-disjoint-tag-packing-ceiling` shows that a
  rank-`r` selector/radical atom admits at most `2^r` pairwise disjoint
  full-mass affine images, no matter how many unconstrained central tag bits
  are adjoined.  Those bits enlarge every source fiber and the target dual by
  the same factor.  This construction works only if the required repetition
  count already lies below that fixed ceiling; it is not a general tagger.
- **Property-T coefficient tagging. Active.** The explicit `G^2<G^3` wall of
  `polynomial-compressor-has-explicit-finite-quotient-wall` is a concrete
  target representation, but
  `fixed-finite-quotient-adjoint-walls-are-canonical-trace-null` prevents a
  fixed quotient copy from carrying positive canonical-profile density.  A
  surviving use must retain the infinite quotient-kernel action while making
  the repeated failure coefficients occupy pairwise disjoint residual types.
