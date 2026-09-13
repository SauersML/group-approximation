---
rg: 2
id: subshift-elementary-group-word-problem-equals-language
kind: claim
title: The word problem of EL_3(LC(X,F_q)⋊Z)/Z is truth-table equivalent to the language of the minimal subshift X
artifacts:
  - research/artifacts/un-open-5-word-problem-degrees-2026-09-13.md
---

Let `X ⊆ A^Z` be an infinite minimal subshift, `q` a prime power, and `S_X = EL_3(LC(X,F_q)⋊Z)/Z`, with the
standard generators `σ_X` of `marked-subshift-elementary-group-determines-language`. Then the word problem of
`(S_X, σ_X)` and the language `L(X)` are truth-table reducible to each other. Both reductions are uniform in `X`.

- `L(X)` to the word problem: the computable map `w ↦ W_w`.
- The word problem to `L(X)`: multiply out the generator matrices over the full-shift crossed product
  `LC(A^Z,F_q) ⋊ Z`, restrict to `X`, and test "off-diagonal zero, diagonal a common scalar" by finitely many
  window queries `v ∈ L_(2m+1)(X)`.
