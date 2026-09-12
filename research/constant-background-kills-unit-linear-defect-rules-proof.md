---
rg: 2
id: constant-background-kills-unit-linear-defect-rules-proof
kind: route
title: Create one defect with the inverse of the linear part on a constant background that the pattern cannot read
target: constant-background-kills-unit-linear-defect-rules
requires: []
artifacts:
  - research/artifacts/unbalanced-design-memory-collisions-2026-09-12.md
---

Artifact, Section 4, Theorem 13, Lemma 12 and Corollary 14.

- **The correction.** With `(L x)(g) = sum_m c_m x(g m)`, composition of automata is the product in
  `F_q[G]`. So `L K delta_1 = delta_1`, and `(K delta_1)(s) = k_(s^-1)`.
- **Window `1`.** The coefficient of `1` in `ell kappa = 1` is nonzero, so `K delta_1` is nonzero on
  `M`. Hence `x|_M != p = x'|_M`.
- **Other windows.** A window `hM` not inside `M ∪ N^-1` reads the background `c` at some address `m`
  in both configurations, and `c != p_m`.
- **Corollary.**
  - The augmentation is a ring homomorphism, so units have nonzero augmentation.
  - For `q = 3`, distinct pairs `{p_m, p_m + t c_m^-1}` miss three distinct symbols, whose sum is
    `0`. If `p` uses every symbol, then `sum c_m = sum c_m^-1 = 0`.
  - An injective linear automaton that is not a unit is not surjective: a bijective linear
    automaton has a linear inverse automaton.
