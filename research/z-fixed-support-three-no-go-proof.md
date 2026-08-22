---
rg: 2
id: z-fixed-support-three-no-go-proof
kind: route
title: Read the two off-base terms in one C3 double-coset cell and normalize the subgroup
target: z-fixed-support-three-elements-cannot-witness
requires:
  - subgroup-supported-one-sided-inverse-rigidity
artifacts:
  - research/artifacts/leavitt-corner-small-rank-coset-classification-2026-08-21.md
---

For a finite support set `X`, the coefficient of every element of a right
coset `rH` in `(sum_X[x])z` is the parity of `|X intersect rH|`.  Thus
`alpha z=z` says that the support meets `H` oddly and every other right coset
evenly.  The equation `z alpha=z` gives the same rule for left cosets.

With three support points, either all three lie in `H`, or exactly one lies in
`H` and the other two lie simultaneously in one non-base right coset and one
non-base left coset.  In the second case write the two points as `x h_1,x h_2`.
Their quotient conjugates the nonidentity element `h_1 h_2^(-1)` of `H` to a
nonidentity element of `H`.  Since `H` has prime order three, `x` normalizes
`H`.  Hence the whole support lies in `K=<H,x>`, where `H` is finite normal
and `K/H` is cyclic.  This `K` is amenable.  The all-in-`H` case is finite.

Therefore `F_2[K]` is directly finite.  The subgroup-supported inverse lemma
projects any partner of `alpha` back into `F_2[K]`, where a right inverse is a
left inverse.  This proves the general claim.  For a corner unitization
`alpha=a+z`, orthogonality of `a in (1-z)S(1-z)` gives
`alpha z=z alpha=z`, and similarly for the other factor.
