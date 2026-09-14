---
rg: 2
id: two-by-two-single-coincidence-classification-proof
kind: route
title: Copy codes and the block rule give strictness, and decoder identities force permutation rules or the surjunctivity of Z in every other case
target: two-by-two-single-coincidence-strict-cores-classified
requires:
  - copy-codes-make-one-sided-table-identities-strict
  - smallest-boolean-strict-core-is-a-one-sided-inverse
  - equal-label-table-is-strict-at-three-symbols-not-two
  - residually-finite-groups-are-surjunctive
  - surjunctivity-is-axiomatized-by-rectangle-clauses
artifacts:
  - research/artifacts/boolean-core-alphabets-and-network-coding-2026-09-12.md
---

Theorem 6.2 and Example 6.4 of the artifact.
- **Strictness.**
  - `O ~ X`, `O ~ B` and `O ~ A` use the copy codes `pi_b, pi_a`, then `pi_b, pi_1`, then
    `pi_1, pi_a` (`copy-codes-make-one-sided-table-identities-strict`).
  - `B ~ A` uses the block rule (`equal-label-table-is-strict-at-three-symbols-not-two`).
- **Never strict.**
  - For `B ~ X`, fixing the shared cell forces every column map `mu(.,w)` to be one bijection `h`,
    so `mu = h o pi_1` and `nu = h^-1 o pi_1`.
  - For `A ~ X`, the diagonal image forces the row images `I_c` to be disjoint singletons, with the
    same conclusion.
- **Kill tables.**
  - For `O ~ B` and `O ~ A`, the decoder identity forces `mu(c,c) = g(c)` or `mu = g o pi_1`, and
    a repeated reverse coincidence feeds `g^-1(d)` to the sink.
  - For `O ~ X` and `B ~ A`, the additive labellings `x_a = 1, x_b = -1` and `x_a = x_b = 1` of
    `Z` realize exactly the forward table and the repeated reverse coincidence. `Z` is surjunctive,
    and the evaluation lemma of the rectangle-clause region applies.
- **Triple coincidence `B ~ A ~ X`.** Every decoding code has column bijections `h_w` with
  `w -> h_w(w)` bijective. So a reverse table with `A' ~ B' ~ X'` returns `d`. The involutions
  `id, (0 2), (0 1)` break every other reverse table.
