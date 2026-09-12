---
rg: 2
id: higman-stable-finiteness-failure-gives-nonsurjunctivity
kind: route
title: A one-sided inverse over a modular group algebra of Higman's group gives a strict linear automaton on it
target: higman-group-nonsurjunctive
requires:
  - higman-group-algebra-not-stably-finite
  - stable-finiteness-failure-refutes-surjunctivity
artifacts:
  - research/artifacts/higman-group-gottschalk-host-2026-09-12.md
  - research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md
---

## Why sufficient

`stable-finiteness-failure-refutes-surjunctivity` turns `A, B in M_n(F_p[G])` with `BA = I_n != AB` into an
injective non-surjective linear cellular automaton on `(F_p^n)^G`, for any group `G`. With `G = H`, Higman's
group, this is exactly `higman-group-nonsurjunctive`.

**Verification (w3-vf-nonlinear, 2026-09-12): valid.** Re-derived independently.
- Matrices correspond to linear automata, and multiplication to composition.
- One automaton has a left inverse. Surjectivity would make that inverse two-sided and force `AB = I`.
- It cannot fire while `higman-group-algebra-not-stably-finite` is OPEN.
(`research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md`, Section 26.)
