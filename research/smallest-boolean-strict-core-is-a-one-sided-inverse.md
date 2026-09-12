---
rg: 2
id: smallest-boolean-strict-core-is-a-one-sided-inverse
kind: claim
title: The two-by-two table x_a x_b = 1 is strict over every alphabet exactly when the reverse table does not repeat the coincidence
distinct_from:
  amenable-decoder-memory-forces-surjectivity: that rules out two-element decoder memories over groups; this classifies the reverse tables that make the smallest coincidence table strict at the Boolean level, where a monoid can realize them.
  triangular-forward-tables-force-surjectivity: that shows one-relator forward tables force bijectivity over groups; this shows the same one-relator forward table admits strict rules over every alphabet exactly when the reverse table does not repeat the relator.
  two-by-two-single-coincidence-strict-cores-classified: that classifies all six single-coincidence 2 x 2 tables with their alphabet thresholds; this is the row x_a x_b = 1, with the bicyclic realization.
artifacts:
  - research/artifacts/boolean-core-alphabets-and-network-coding-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

**ESTABLISHED** by `smallest-boolean-strict-core-proof`.

Let `S = {1,a}` and `M = {1,b}`, and let `T_f` be the forward table whose only coincidence is
`(a,b) ~ (1,1)`. For a reverse table `T_r` these are equivalent:
1. some alphabet admits strict rules for `(T_f, T_r)`;
2. every alphabet with at least two symbols does, via the column copy `mu(u,v) = v`,
   `nu(y_1, y_a) = y_a`;
3. `T_r` does not identify `(b,a)` with `(1,1)`.

**Realizations.** The strict data `(T_f, discrete)` are realized by a one-sided inverse
`x_a = t`, `x_b = s` in the bicyclic monoid `< s, t | ts = 1 >`. No group realizes them.

For this table, strict rules exist uniformly over every alphabet with at least two symbols, and
the one obstruction is that a one-sided inverse in a group is two-sided.

It is not the only strict 2 x 2 core. `two-by-two-single-coincidence-strict-cores-classified` shows
that `x_b = 1` and `x_a = 1` are strict through copy codes, and that `x_a = x_b` is strict over
three or more symbols but not over two. For group-realized 2 x 2 data the reverse table is always the transpose of
the forward table, so these shapes never give counterexamples.

Proof: Section 4 of the artifact.
