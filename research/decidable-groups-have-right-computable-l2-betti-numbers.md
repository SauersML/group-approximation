---
rg: 2
id: decidable-groups-have-right-computable-l2-betti-numbers
kind: claim
title: Kernel dimensions over a decidable group are right-computable reals, and computable under the determinant conjecture
distinct_from:
  determinant-conjecture-holds-for-sofic-groups: that is the determinant bound for sofic groups; this converts any determinant bound, sofic or not, into computability of kernel dimensions over groups with decidable word problem.
---

**ESTABLISHED (literature, with a self-contained proof in the route).** Let `G` be a finitely
generated group with decidable word problem, and `T in M_k(Q[G])`.
1. `dim_vN ker T` is the infimum of a computable decreasing sequence of rationals. So it is a
   right-computable (upper semicomputable) real.
2. If `G` satisfies Lück's determinant conjecture, `dim_vN ker T` is a computable real, with an
   explicit modulus in terms of `k`, the coefficients of `T`, and the denominators.

**Credit.** This is the Turing-degree-0 case of C. Löh and M. Uschold, *L2-Betti numbers and
computability of reals*, arXiv:2202.03159v4:
- **Theorem 1.1**: "Let G be a finitely generated group with word problem of degree at most a.
  Moreover, let m,n ∈ N and A ∈ M_(m×n)(ZG). Then, the L2-Betti number dim ker(R_A^(2)) is
  a-right-computable."
- **Theorem 1.2**: effective convergence for matrices of determinant class, given a rational
  witness.

They record that "In Turing degree 0, the corresponding versions of Theorem 1.1 and Theorem 1.2
had already been established by Groth [Gro12]" (T. Groth, BSc thesis, 2012). **Theorem 1.4**
realizes exactly the nonnegative a-computable reals from finitely generated groups of
determinant class with word problem of degree at most a. Grabowski remarks the sofic case
(arXiv:1004.2030, Section 1c). The route gives a short proof of the degree-0 statements, not a
new theorem. Read from PDF text on MSI, 2026-09-12.

Route: `decidable-groups-right-computable-l2-betti-proof`.
