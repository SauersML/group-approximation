---
rg: 2
id: binary-leavitt-algebra-is-purely-infinite-by-monomials
kind: claim
title: Every nonzero element of the binary Leavitt algebra is carried to one by two monomials
distinct_from:
  agp-purely-infinite-simple-k1-is-unit-abelianization: that is the cited K_1 theorem for purely infinite simple rings; this is the elementary monomial compression property of one Leavitt algebra, proved in place and used for idempotent equivalence rather than for K_1.
  binary-leavitt-algebra-not-directly-finite: that is the single one-sided inverse t_0 s_0 = 1 != s_0 t_0; this says every nonzero element is carried to 1 by a left and a right monomial.
artifacts:
  - research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md
  - research/artifacts/gottschalk-negative-side-verification-2026-09-12.md
---

Let `R = L_(F_2)(1,2)` with `t_i s_j = delta_ij` and `s_0 t_0 + s_1 t_1 = 1`,
and write `S[alpha] = s_(alpha_1) ... s_(alpha_k)`,
`T[beta] = t_(beta_l) ... t_(beta_1)`. For every nonzero `x` in `R` there are
words `alpha*`, `gamma`, `w` over `{0,1}` with

    T[w] T[alpha*] x S[gamma] S[w] = 1.

This is the monomial form of pure infiniteness. The proof (Section 1 of the
artifact) uses the relations and nothing else:

* right multiplication by a long word turns `x` into a nonzero sum of words
  `S[alpha]`, since `sum_(|gamma|=m) S[gamma] T[gamma] = 1`;
* the left inverse of a longest word gives `1 + sum_(delta) T[delta]` over
  nonempty `delta` of distinct lengths;
* conjugating by `w = 0 1^L` kills every tail.

Linear independence of the words is proved through the representation on
sequences that are not eventually periodic.
