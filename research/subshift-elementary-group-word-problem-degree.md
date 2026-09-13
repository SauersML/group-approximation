---
rg: 2
id: subshift-elementary-group-word-problem-degree
kind: claim
title: The word problem of EL_3 over a minimal subshift algebra has exactly the Turing degree of the subshift language
distinct_from:
  lef-kazhdan-group-without-finite-quotients-exists: that proves existence of one infinite LEF Kazhdan group without finite quotients; this computes the word-problem degree of the whole family and obtains uncountably many isomorphism classes, one for every Turing degree.
artifacts:
  - research/artifacts/subshift-elementary-group-turing-degrees-2026-09-12.md
---

Let `X` be an infinite minimal subshift, `R_X = LC(X,F_q) ⋊ Z` and `G_X = EL_3(R_X)`. Then

```text
WP(G_X)  ≡_T  L(X)       (L(X) = the language of X).
```

The same holds for the word problem of `G_X / Z(G_X)`.

For the Sturmian subshift `X_α`, `L(X_α) ≡_T α`. Consequently:

- for every Turing degree `d` there is an infinite, finitely generated LEF Kazhdan group without
  nontrivial finite quotients whose word problem has degree `d`;
- these groups form uncountably many isomorphism classes;
- computable slopes, for example Fibonacci, give decidable word problem.
