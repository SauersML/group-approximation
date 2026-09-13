---
rg: 2
id: decidable-groups-have-right-computable-l2-betti-numbers
kind: claim
title: Kernel dimensions over a decidable group are right-computable reals, and computable under the determinant conjecture
distinct_from:
  determinant-conjecture-holds-for-sofic-groups: that is the determinant bound for sofic groups; this converts any determinant bound, sofic or not, into computability of kernel dimensions over groups with decidable word problem.
---

**ESTABLISHED (proved on paper, unreviewed).** Let `G` be a finitely generated group with
decidable word problem, and `T in M_k(Q[G])`.
1. `dim_vN ker T` is the infimum of a computable decreasing sequence of rationals. So it is a
   right-computable (upper semicomputable) real.
2. If `G` satisfies Lück's determinant conjecture, `dim_vN ker T` is a computable real, with an
   explicit modulus in terms of `k`, the coefficients of `T`, and the denominators.

The idea of 2 is remarked by Grabowski for sofic groups (arXiv:1004.2030, Section 1c, after
Question 1). Here it is stated for any decidable group satisfying the conjecture.

Route: `decidable-groups-right-computable-l2-betti-proof`.
