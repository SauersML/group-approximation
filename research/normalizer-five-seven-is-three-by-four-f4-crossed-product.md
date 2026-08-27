---
rg: 2
id: normalizer-five-seven-is-three-by-four-f4-crossed-product
kind: claim
title: The normalizer five-by-seven branch is exactly a three-by-four F4 crossed-product problem
distinct_from:
  constant-c3-normalizer-is-f4-leavitt-semilinear: that computes the normalizer group; this computes the exact compressed support ranks and eliminates one of its two rank-five incidence types.
  z-fixed-support-five-hecke-normal-form: that separates normalizer and rectangle supports before compression; this resolves the three-base-term normalizer subcase and identifies the sole survivor.
  rank-five-rectangle-is-one-letter-hecke-element: that treats the outside-normalizer branch; this treats the complementary inside-normalizer branch and explains why there is no iterative finite-field reduction.
artifacts:
  - research/artifacts/five-seven-coefficient-and-adjoint-audit-2026-08-21.md
---

Let `H=C_3`, `e=1+sum_H[h]`, and `N=N_G(H)`.  The corner `eF_2[N]e` is a
crossed product with coefficient field `eF_2[H]e=F_4` and quotient `N/H`.
If a `z`-fixed normalizer-supported five-term factor uses all three base-cell
elements, its corner compression is a single nonzero coefficient times one
quotient monomial, hence is invertible and cannot witness failure of direct
finiteness.  The sole factor uses one base element and two doubled normalizer
cells, and compresses to three monomials.  A partner with three base elements
compresses to a binomial over one cyclic quotient subgroup; its finite-by-
cyclic corner is amenable and directly finite, so that case is impossible.
The sole partner has one base element and three doubled cells and compresses
to exactly four monomials.

For the binary Leavitt unit group this is a `3`-by-`4` inverse problem
over the `F_4` crossed product of the projective semilinear quotient described
by `constant-c3-normalizer-is-f4-leavitt-semilinear`.  It is not an ordinary
`F_4` group-ring instance, and there is no justified induction to `F_16`.
