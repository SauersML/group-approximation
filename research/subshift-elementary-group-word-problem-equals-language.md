---
rg: 2
id: subshift-elementary-group-word-problem-equals-language
kind: claim
title: The word problem of EL_3(LC(X,F_q)⋊Z)/Z is truth-table equivalent to the language of the minimal subshift X
distinct_from:
  subshift-elementary-group-word-problem-degree: that proves WP(G_X) ≡_T L(X) ≡_T WP(S_X) (2026-09-12, reviewed PASS); this refines both reductions to truth-table reductions, uniform in X.
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

**Review (un-verify-open, 2026-09-13, `research/artifacts/un-review-open-2026-09-13-part1.md` §1.3): PASS.** The
full-shift normal form, the restriction homomorphism `π`, the vanishing test on `L_(2m+1)(X)` and the scalar test
over the finitely many `c ∈ F_q` were re-derived; the queries are computed from `g` in advance, so the reduction is
truth-table. The Turing form is already on main (`distinct_from`); the truth-table refinement is the new part.
