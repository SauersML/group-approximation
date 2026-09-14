---
rg: 2
id: cyclic-corner-fullness-refutes-leavitt-host-surjunctivity
kind: route
title: Pad a Leavitt-visible corner solution by the other scalar factors to get a one-sided pair
target: some-finite-field-leavitt-unit-group-nonsurjunctive
requires:
  - leavitt-visible-cyclic-corner-is-full-on-some-host
  - leavitt-unit-group-algebras-split-over-scalar-characters
  - stable-finiteness-reduces-to-prime-field
  - stable-finiteness-failure-refutes-surjunctivity
artifacts:
  - research/artifacts/leavitt-host-survey-scalar-characters-2026-09-12.md
---

Given `c' e_H b' = eps_iota` in `A_iota`, put `A' = e_H b' + (1 - eps_iota)` and
`C = c' + (1 - eps_iota)`. Then `C A' = 1`.

`A' C != 1`, because `A' C = e_H b' c' e_H + (1 - eps_iota)` would otherwise force
`e_H b' c' e_H = eps_iota`, hence `e_H = eps_iota`. That fails: `e_H = eps_iota` would give
`[g] eps_iota = eps_iota`, and since the evaluation factors through `A_iota`, `g = 1` in the Leavitt
algebra, which is false for `m >= 2`.

So `F_q[L_(F_q)(1,d)^x]` is not directly finite. By `stable-finiteness-reduces-to-prime-field`,
`F_p` of the same group is not stably finite. By `stable-finiteness-failure-refutes-surjunctivity`
the group carries an injective, non-surjective linear automaton over a finite alphabet.
