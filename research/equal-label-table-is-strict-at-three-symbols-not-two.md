---
rg: 2
id: equal-label-table-is-strict-at-three-symbols-not-two
kind: claim
title: The two-by-two table x_a = x_b with a discrete reverse table has strict rules over every alphabet with at least three symbols and over none with two
distinct_from:
  surjunctivity-failure-descends-to-binary-alphabet: that asks whether a group's strictness descends to two symbols once the memories and tables may change; this shows descent with the tables held fixed is false.
  strict-rule-pairs-pass-to-product-alphabets: that moves strictness up along multiples of the alphabet size; this shows it cannot always be moved down, with a table whose admissible sizes are exactly n >= 3.
artifacts:
  - research/artifacts/boolean-core-alphabets-and-network-coding-2026-09-12.md
---

**ESTABLISHED** by `equal-label-table-three-symbol-threshold-proof`.

Let `S = {1,a}`, `M = {1,b}`, let `T_f` identify only `(1,b)` with `(a,1)` (read in groups as
`x_a = x_b`), and let `T_r` be discrete, or more generally any table separating `(1,a)` from
`(b,1)`.

- **Three or more symbols.** Split `A` into `P = {0,1}` and `Q = A \ P`, put `g_P = id` and
  `g_Q = (0 1)`, and write `B(z)` for the block of `z`. The rule
  `mu(u,v) = nu(u,v) = g_B(v)(u)` satisfies the decoder identity on `T_f` and fails the reverse
  identity on `T_r`.
- **Two symbols.** Every pair `(mu, nu)` satisfying the decoder identity on `T_f` has the form
  `mu = h o pi_1`, `nu = h^-1 o pi_1`. It therefore satisfies the reverse identity on every table.

So the alphabet sizes admitting strict rules for these fixed tables are exactly `n >= 3`, and
strictness for fixed tables does not descend to two symbols. A repeated reverse coincidence
`(1,a) ~ (b,1)` kills strictness over every alphabet, since the labelling `x_a = x_b = 1` of `Z`
realizes it.

Proof: Theorem 6.2, rows `B ~ A`, and Corollary 6.3 of the artifact.
