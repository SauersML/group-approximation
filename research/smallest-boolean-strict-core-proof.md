---
rg: 2
id: smallest-boolean-strict-core-proof
kind: route
title: Column copy breaks every reverse table that separates the transposed cell, and Z forces the reverse identity otherwise
target: smallest-boolean-strict-core-is-a-one-sided-inverse
requires:
  - residually-finite-groups-are-surjunctive
  - surjunctivity-is-axiomatized-by-rectangle-clauses
artifacts:
  - research/artifacts/boolean-core-alphabets-and-network-coding-2026-09-12.md
---

Section 4 of the artifact.
- **Column copy.** The column copy satisfies `Dec(T_f)`, because relay `a` reads `p(a,b) = p(1,1)`.
  Its transposed composite returns `q(b,a)`, so `Enc` fails exactly when `T_r` separates `(b,a)`
  from `(1,1)`.
- **The repeated coincidence.** Otherwise `T_r` contains `T_0 = {(b,a) ~ (1,1)}`. In additive `Z`,
  `x_a = 1` and `x_b = -1` realize exactly `(T_f, T_0)`.
  1. `Z` is residually finite, hence surjunctive.
  2. By the evaluation lemma in the rectangle-clause region, `Dec(T_f)` makes `tau` injective,
     hence bijective, which is `Enc(T_0)`.
  3. Coarsening gives `Enc(T_r)`.
