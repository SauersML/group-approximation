---
rg: 2
id: anti-central-state-obstruction-proof
kind: route
title: Halve the unit class with the sign unit, then apply the Hahn–Banach state criterion
target: anti-central-state-obstruction-equals-stable-finiteness
requires:
  - ternary-leavitt-swap-problem-splits-at-central-involution
  - stable-finiteness-failure-refutes-surjunctivity
artifacts:
  - research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md
---

## Why sufficient

- **Halving.** The split supplies `[d] e_- [d] = eps_- - e_-`, so `[eps_-] = 2[e_-]`.
- **Part 1.**
  - A corner solution gives an idempotent `f = (e_- b)(c e_-) <= e_-` with `f ~ eps_-`. So
    `[e_-] = [eps_-] + [e_- - f]`, that is, `u <= [e_-]`.
  - Then `2[e_-] <= [e_-]`, so `[e_-] <= 0` and `u <= 0`.
  - States and normalized Sylvester rank functions are monotone, so neither exists.
  - `f` and `[d] f [d]` are orthogonal idempotents equivalent to `eps_-`, so `S_-` is properly infinite.
- **Part 2.**
  - `u` is an order unit.
  - `p(x) = inf{ m/n : n x <= m u }` is a finite sublinear functional with `p(+-u) = +-1` exactly when
    no `k u <= 0`.
  - Hahn–Banach gives an additive `f <= p` with `f(u) = 1`, and positivity follows from `p(-x) <= 0`
    on the cone.
- **Part 3.**
  - `[Q] + k u = 0` gives `S_-^r ~= S_-^r (+) S_-^k (+) Q`, a one-sided pair in `M_r(S_-)`.
  - Padding with `eps_+` gives a pair in `M_r(F_3[G])`.
  - The stable-finiteness lemma then yields a strict automaton.

Sections 1–3 of the artifact.
