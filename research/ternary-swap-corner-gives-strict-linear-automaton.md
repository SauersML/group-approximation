---
rg: 2
id: ternary-swap-corner-gives-strict-linear-automaton
kind: route
title: A full swap-averaging idempotent gives an injective linear automaton with swap-invariant output over F_3
target: ternary-leavitt-unit-group-nonsurjunctive
requires: [ternary-leavitt-swap-idempotent-is-full, linear-invariant-output-automata-fail-augmentation, invariant-output-injective-automata-need-invisible-symmetry]
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

From `c e b = 1` in `F_3[G_3]`, put `a = e b`. Then `w a = a`, so the linear
automaton `tau_a` over `F_3` has output invariant under `<w>`, and `tau_c tau_a = id`
makes it injective. By the invariant-output theorem it misses every configuration
that is not right-`<w>`-invariant, so it is not surjective. Section 6 of the
artifact.
