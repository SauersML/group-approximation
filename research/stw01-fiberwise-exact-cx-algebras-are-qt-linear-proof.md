---
rg: 2
id: stw01-fiberwise-exact-cx-algebras-are-qt-linear-proof
kind: route
title: Haagerup's exact case on each fiber, glued by the central fiber principle
target: stw01-fiberwise-exact-cx-algebras-are-qt-linear
requires:
  - stw01-central-cx-fibers-preserve-qt-linearity
artifacts:
  - research/artifacts/stw01-central-fiber-qt-linearity-2026-09-16.md
---

Fix `x in X`.

- If `J_x = A`, then `A_x = 0` and there is nothing to prove.
- Otherwise `A_x` is a nonzero unital C\*-algebra, with unit the image of `1_A`, and
  it is exact by hypothesis.

Haagerup, *Quasitraces on exact C\*-algebras are traces*, C. R. Math. Rep. Acad.
Sci. Canada 36 (2014), Theorem 5.11, states that quasitraces on exact unital
C\*-algebras are traces.  His quasitraces satisfy Definition 3.1, which includes
the `M_2` witness, so they are exactly the bounded 2-quasitraces used here.  The
theorem is stated for normalized quasitraces.  A nonzero bounded 2-quasitrace
`tau` has `tau(1) > 0`, since `tau(1) = 0` forces `tau = 0` by positivity on
`C*(1, a)`, and `tau / tau(1)` is normalized.  So every bounded 2-quasitrace on
`A_x` is a trace.

This holds for every `x in X`.  The "if" direction of
`stw01-central-cx-fibers-preserve-qt-linearity`, applied to the same `theta`, gives
that every bounded 2-quasitrace on `A` is a trace.  QED.
