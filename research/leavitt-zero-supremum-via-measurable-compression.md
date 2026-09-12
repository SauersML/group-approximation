---
rg: 2
id: leavitt-zero-supremum-via-measurable-compression
kind: route
title: Count the one-coordinate partition of a measurable compression and apply the zero-or-infinity dichotomy
target: leavitt-units-have-zero-rokhlin-entropy-supremum
requires: [measurable-alphabet-compression-over-leavitt-units, seward-per-group-rokhlin-entropy-of-bernoulli-shifts, positive-rokhlin-entropy-makes-leavitt-units-surjunctive]
artifacts:
  - research/artifacts/measurable-alphabet-compression-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Section 1 of the artifact. Let `tau: A^U -> B^U` be the code given by the first prerequisite. The
partition `beta = {tau(x)(1) = b}` has `|B|` pieces, and its translates recover `tau(x)`. By
Lusin–Souslin, `tau(x)` determines `x` on a conull Borel set. So `beta` generates, and
`h^Rok_U(A^U) <= log |B| < log |A|`.

By item 1 of the second prerequisite, `h^Rok_U(A^U) = min{ log |A|, h_sup(U) }`, so
`h_sup(U) < log |A| < infinity`. Part 1 of the third prerequisite makes `h_sup(U)` zero or infinite,
so it is zero, and every free ergodic action of finite Rokhlin entropy has entropy `0`. A free ergodic
action of infinite Rokhlin entropy would be POS(`U`), which part 2 of the third prerequisite makes
equivalent to INF(`U`), contradicting `h_sup(U) = 0`. That is the target.

The first prerequisite is open, so this route establishes nothing yet.
