---
rg: 2
id: scaling-family-pairwise-nonisomorphic
kind: claim
title: Pairwise non-isomorphism of the non-MF scaling family
root: true
distinct_from:
  scaling-family-non-mf: The established claim proves non-MF for every scale but does not distinguish the abstract isomorphism types.
  continuum-nonisomorphic-non-mf-cylinder: This claim distinguishes the explicit countable scaling family; the other asks for a continuum-sized family in the marked-group cylinder.
artifacts:
  - non_mf_groups_exist.tex
  - notes/NON_MF_FINAL_REVIEW_AND_RESOLUTION_2026-08-14.md
---

The finitely presented non-MF groups `E_m`, for integers `m >= 2`, are
pairwise non-isomorphic.


## Prime subfamily solved

The prime-indexed subfamily is now completely separated by
`prime-scaling-subfamily-pairwise-nonisomorphic`.  For prime `p`, the
maximal property-`(T)` subgroups of `E_p` have finite radical
`ClLamp(p^3)`, of order `2^(p^3+1)`; this intrinsic number recovers `p`.

The full root remains open only for comparisons involving composite scales.
There the marked orbital block is no longer complete: its edge differences
are the unimodular vectors in `(Z/mZ)^3`, so the prime proof cannot be
relabelled with `p=m`.
