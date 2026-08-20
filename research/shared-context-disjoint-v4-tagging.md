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

## Attempts

- **Parent exclusivity. Unnecessary.**
  `constant-repetition-v4-needs-only-disjoint-tags` replaces it by a fixed
  number of duplicate batches and the ambient identity capacity.
- **Independent context tags. Dead.** They do not arise from a common target
  representation and do not constrain cross-Gram products.
- **Fixed HNN character atlas. Dead.** The regular stationary type flow
  absorbs every finite list of subgroup character identifications.
- **Property-T coefficient tagging. Active.** The explicit `G^2<G^3` wall of
  `polynomial-compressor-has-explicit-finite-quotient-wall` is a concrete
  target representation; the remaining task is to make the repeated failure
  atom coefficients occupy pairwise disjoint wall types.
