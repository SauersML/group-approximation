---
rg: 2
id: nonpositive-unit-class-refutes-ternary-surjunctivity
kind: route
title: A nonpositive multiple of the anti-central unit class gives a one-sided pair of matrices over the ternary group algebra
target: ternary-leavitt-unit-group-nonsurjunctive
requires:
  - ternary-anti-central-unit-class-is-nonpositive
  - stable-finiteness-failure-refutes-surjunctivity
artifacts:
  - research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md
---

## Why sufficient

- **One-sided pair over `S_-`.** `S_-^r ~= S_-^r (+) (S_-^k (+) Q)` with `k >= 1` is an isomorphism onto
  a proper summand, so there are `A, B` in `M_r(S_-)` with `BA = 1_r != AB`.
- **Padding.** `A + eps_+ 1_r` and `B + eps_+ 1_r` are a one-sided pair in `M_r(F_3[G_3])`.
- **Automaton.** The stable-finiteness lemma turns the pair into an injective non-surjective linear
  automaton on `(F_3^r)^(G_3)`.

Theorem A(c) of the artifact.
