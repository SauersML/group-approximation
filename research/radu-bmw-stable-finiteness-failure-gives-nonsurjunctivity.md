---
rg: 2
id: radu-bmw-stable-finiteness-failure-gives-nonsurjunctivity
kind: route
title: A one-sided inverse over a modular group algebra of Radu's lattice gives a strict linear automaton on it
target: radu-bmw-lattice-nonsurjunctive
requires:
  - radu-bmw-lattice-group-algebra-not-stably-finite
  - stable-finiteness-failure-refutes-surjunctivity
artifacts:
  - research/artifacts/radu-lattice-strict-automaton-screens-2026-09-12.md
---

## Why sufficient

`stable-finiteness-failure-refutes-surjunctivity` turns `A, B in M_n(F_p[G])` with `B A = I_n != A B`
into an injective non-surjective linear cellular automaton on `(F_p^n)^G`, for any group `G`. With
`G = Gamma_R`, this is exactly `radu-bmw-lattice-nonsurjunctive`.
