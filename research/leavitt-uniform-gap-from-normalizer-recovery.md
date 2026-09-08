---
rg: 2
id: leavitt-uniform-gap-from-normalizer-recovery
kind: route
title: Contradict the blockwise exclusion with a recovery of the error-basis class
target: leavitt-24k-feasibility-has-a-uniform-gap
requires:
  - leavitt-24k-models-avoid-blockwise-error-basis-normalizers
  - hyperlinear-leavitt-models-reduce-to-error-basis-normalizers
artifacts:
  - research/artifacts/leavitt-error-basis-normalizer-obstruction-2026-09-08.md
---

If both prerequisites hold, take any sequence of regular-factor tuples
whose `T`-defects tend to zero. The recovery claim sends `delta(X_n)`
to zero; the exclusion forces
`A_0 epsilon_n + B_0 delta(X_n) >= 1/sqrt 2` with `epsilon_n -> 0`.
That is a contradiction, so no such sequence exists: some `eta > 0`
bounds `max_(r in T) ||r(X)-I||_2` below, uniformly in `k` and `U`.
Since `T` is finite and the computable families `T_m` of
`binary-leavitt-hyperlinear-iff-24k-feasible` increase to `ker q`, some
`T_m` contains `T`, and that `m` witnesses the target.

**Read this route as a record of where the argument stops, not as an
easier target.** Its second prerequisite is strictly stronger than the
target: it is refuted outright if the group is hyperlinear, whereas the
target is merely equivalent to nonhyperlinearity. So the decomposition
buys the explicit constants and the exclusion of the Clifford
architecture, and leaves a hole that is at least as hard as the original
question. The first prerequisite is the part that is actually finished.
