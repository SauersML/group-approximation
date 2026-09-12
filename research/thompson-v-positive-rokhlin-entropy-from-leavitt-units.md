---
rg: 2
id: thompson-v-positive-rokhlin-entropy-from-leavitt-units
kind: route
title: Positive Rokhlin entropy over the Leavitt units makes them maximal, and maximality descends to their copy of V
target: thompson-v-has-positive-rokhlin-entropy-action
requires:
  - leavitt-unit-group-has-positive-rokhlin-entropy-action
  - positive-rokhlin-entropy-makes-leavitt-units-surjunctive
  - leavitt-cylinder-swaps-generate-thompson-in-el
  - bernoulli-rokhlin-maximality-passes-to-subgroups
artifacts:
  - research/artifacts/rokhlin-co-amenable-ascent-and-thompson-v-2026-09-12.md
---

Section 3 of the artifact. Let `U = L_(F_2)(1,2)^x`.

1. **U is maximal.** Positive Rokhlin entropy of one free ergodic action of U gives RBS(U) by item 2 of `positive-rokhlin-entropy-makes-leavitt-units-surjunctive`. So `h^Rok_U((A^k)^U) = k log |A|` for every finite A and k: U is Rokhlin-maximal at every q.
2. **V inside U.** `V <= U` by `leavitt-cylinder-swaps-generate-thompson-in-el`, through `V <= EL_D(R) <= U`.
3. **Descent.** Maximality passes to subgroups (item 1 of `bernoulli-rokhlin-maximality-passes-to-subgroups`). So the Bernoulli 2-shift over V has Rokhlin entropy `log 2 > 0`. It is free and ergodic, which is the target.

The first prerequisite is open, so this route establishes nothing yet.
