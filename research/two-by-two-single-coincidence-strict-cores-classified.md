---
rg: 2
id: two-by-two-single-coincidence-strict-cores-classified
kind: claim
title: Among the six single-coincidence two-by-two tables, four are strict cores with explicit reverse thresholds and two are never strict
distinct_from:
  smallest-boolean-strict-core-is-a-one-sided-inverse: that is the row x_a x_b = 1; this classifies all six single-coincidence tables and their alphabet thresholds.
  amenable-decoder-memory-forces-surjectivity: that excludes two-element decoder memories over groups; this works at the Boolean level, where the reverse table is free, and finds which 2 x 2 tables carry strict rules at all.
  triangular-forward-tables-force-surjectivity: that is a group-level exclusion; this is table-level combinatorics, including tables no group or monoid realizes.
artifacts:
  - research/artifacts/boolean-core-alphabets-and-network-coding-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

**ESTABLISHED** by `two-by-two-single-coincidence-classification-proof`.

Let `S = {1,a}` and `M = {1,b}`. Name the forward cells `O = (1,1)`, `B = (1,b)`, `A = (a,1)` and
`X = (a,b)`, and their transposes `O', B' = (b,1), A' = (1,a), X' = (b,a)`. Let `T_f` have exactly
one coincidence. Strict rules exist for `(T_f, T_r)` exactly as follows.

| coincidence | group reading | strict iff `T_r` | alphabets |
|---|---|---|---|
| `O ~ X` | `x_a x_b = 1` | separates `X'` from `O'` | every size `>= 2` (copy code) |
| `O ~ B` | `x_b = 1` | separates `B'` from `O'` | every size `>= 2` (copy code) |
| `O ~ A` | `x_a = 1` | separates `A'` from `O'` | every size `>= 2` (copy code) |
| `B ~ A` | `x_a = x_b` | separates `A'` from `B'` | every size `>= 3`; not size 2 |
| `B ~ X` | `x_b = x_a x_b` | never | none |
| `A ~ X` | `x_a = x_a x_b` | never | none |

**The `x_a = x_b` row.** The strict code over three or more symbols is the block rule
`mu(u,v) = nu(u,v) = g_B(v)(u)`. Here the blocks are `{0,1}` and the rest, `g = id` on the first
block's symbols and `g = (0 1)` on the second's. The relay reading the shared cell reveals its
block, and the other relay's output is unmasked by the corresponding involution.

**Triple coincidence.** `B ~ A ~ X` is strict iff `T_r` does not contain `{A' ~ B' ~ X'}`, over
three or more symbols and never over two. So it is strict even for some reverse tables that repeat
`A' ~ B'` (Example 6.4).

Thus the claim "the only strict 2 x 2 core is a one-sided inverse" is false at the Boolean level.
The kill tables need not be reverse tables realized by any group or monoid. All these tables are
excluded as counterexamples, because group-realized 2 x 2 reverse tables are transposes.

Proof: Theorem 6.2 and Example 6.4 of the artifact.
