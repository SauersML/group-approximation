---
rg: 2
id: h31-seven-central-image-criterion
kind: claim
title: The explicit hyperbolic Kazhdan group H31 has an exact central-seven cohomology criterion
artifacts:
  - research/artifacts/rips-central-pullback-finite-image-centers-2026-09-12.md
distinct_from:
  hyperbolic-finite-images-exclude-a-central-prime: that is an existence question requiring an input with a uniform restriction on finite images; this establishes the geometry and an exact criterion for the particular candidate H31 without asserting that it satisfies the restriction.
---

Let `H_31` be the group with the explicit presentation in Theorem 1.2
of Caprace--Conder--Kaluba--Witzel, *Hyperbolic generalized triangle
groups, property (T) and finite simple quotients*. Its presentation is
reproduced in the attached artifact.

The group `H_31` is infinite, non-elementary word-hyperbolic, and has
property (T). The following statements are equivalent:

1. Every finite image of `H_31` has center of order prime to `7`.
2. For every finite-index normal subgroup `L` of `H_31`,
   `H^1(L;F_7)^(H_31)=0`.
3. For every finite quotient `F` of `H_31`, `H^2(F;F_7)=0`, with
   trivial coefficient action.

Moreover, setting `c=1` in the presentation gives a retraction onto
`PSL_2(31)`. Its kernel `K` satisfies `H^j(K;F_p)=0` for every
`j>0` and every prime `p!=5`.

This claim establishes the equivalence and the first-kernel vanishing.
It does not assert any of statements 1--3. Statement 3 is isolated as
the open input [[h31-finite-quotients-have-no-seven-schur-class]].
