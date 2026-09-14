---
rg: 2
id: projective-swap-corner-gives-strict-automaton
kind: route
title: A full swap-averaging idempotent on the scalar quotient gives a strict linear automaton there
target: projective-ternary-leavitt-group-nonsurjunctive
requires: [projective-ternary-swap-idempotent-is-full, linear-invariant-output-automata-fail-augmentation, invariant-output-injective-automata-need-invisible-symmetry]
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

From `c ebar b = 1` in `F_3[PG]` put `a = ebar b`. Then `wbar a = a`, so the
linear automaton of `a` over `F_3` has `<wbar>`-invariant output, and the linear
automaton of `c` is a left inverse. By the invariant-output theorem it misses
every configuration that is not right-`<wbar>`-invariant, so it is not surjective.
