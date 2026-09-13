---
rg: 2
id: subshift-elementary-group-word-problem-degree-proof
kind: route
title: Normal forms reduce the word problem to the language, and cylinder roots reduce the language to the word problem
target: subshift-elementary-group-word-problem-degree
requires: [minimal-subshift-algebra-is-simple-lef-ring, lef-kazhdan-group-without-finite-quotients-exists]
artifacts:
  - research/artifacts/subshift-elementary-group-turing-degrees-2026-09-12.md
---

Complete derivation in the artifact.

- **`WP <=_T L(X)`.** Matrix entries are kept in the normal form `sum F_j u^j`, with window tables
  `F_j`. The product rule is local, and an entry vanishes iff its tables vanish on
  `L_(2r+1)(X)`. Scalar matrices are detected the same way.
- **`L(X) <=_T WP`.** `chi_w = prod_i u^(-i) chi_[x_0=w_i] u^i` is nonzero iff `w ∈ L(X)`. A group
  word for `e_12(chi_w)` is computable through `e_12(ab) = [e_13(a), e_32(b)]` and conjugation of
  roots by `u^(±i)` through two commutators. A nontrivial root is not scalar.
- **Sturmian degrees.** `L(X_α) <=_T α` by the rotation coding. `α <=_T L(X_α)` because factors of
  length `n` are balanced, `|#1 - nα| < 1`.
- **Isomorphism classes.** Isomorphic finitely generated groups have Turing-equivalent word
  problems. There are uncountably many degrees, and each `G_(X_α)` is an infinite LEF Kazhdan group
  without finite quotients (`lef-kazhdan-group-without-finite-quotients-exists`).
