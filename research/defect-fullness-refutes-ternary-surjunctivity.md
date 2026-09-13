---
rg: 2
id: defect-fullness-refutes-ternary-surjunctivity
kind: route
title: A two-root defect full modulo the weakly finite reflection ideal gives a stage-one stable finiteness failure
target: ternary-leavitt-unit-group-nonsurjunctive
requires: [ternary-defect-is-full-in-largest-weakly-finite-image, weakly-finite-reflection-ideal-detects-weakly-finite-images, stable-finiteness-failure-refutes-surjunctivity]
artifacts:
  - research/artifacts/weakly-finite-image-defect-fullness-2026-09-12.md
---

1. Write `eps_- = j + sum_i a_i D b_i` with `j ∈ J_omega(S_-)`.
2. The evaluation `pi : S_- -> L_(F_3)(1,2)` sends `eps_-` to `1` and `D` to `e_23 e_12 = 0`. So `pi(j) = 1`, and
   `J_omega != 0`.
3. By item (d) of the reflection ideal claim, `J_1(S_-) != 0`: some square matrix over `S_-` has a one-sided inverse
   and is not invertible.
4. `S_-` is a direct factor of `F_3[G]`, so `F_3[G]` is not stably finite.
5. `stable-finiteness-failure-refutes-surjunctivity` gives the target.

This is artifact Theorem 3.1(c). The route does not use `ternary-anti-central-defect-ideal-is-the-evaluation-kernel`.
