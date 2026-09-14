---
rg: 2
id: ternary-invisible-pair-refutes-surjunctivity
kind: route
title: An invisible pair on the anti-central summand is a direct-finiteness failure of the ternary group algebra
target: ternary-leavitt-unit-group-nonsurjunctive
requires: [ternary-anti-central-kernel-unitization-not-directly-finite, ternary-leavitt-swap-problem-splits-at-central-involution, stable-finiteness-failure-refutes-surjunctivity]
artifacts:
  - research/artifacts/ternary-anti-central-kernel-normal-forms-2026-09-12.md
---

From `(eps_- + v)(eps_- + u) = eps_- != (eps_- + u)(eps_- + v)` in `S_-`, put
`A = (eps_- + u) + eps_+` and `C = (eps_- + v) + eps_+`.
* The idempotents `eps_+-` are central, orthogonal and sum to `1`.
* So `C A = 1` and `A C != 1` in `F_3[G]`.

`stable-finiteness-failure-refutes-surjunctivity` then gives an injective, non-surjective linear
automaton on the full shift over `G`.
