---
rg: 2
id: one-transvection-s0-lift-refutes-ternary-surjunctivity
kind: route
title: Turn a corner left inverse of the one-transvection transition into a one-sided unit of F_3[G] and feed it to the linear-automaton criterion
target: ternary-leavitt-unit-group-nonsurjunctive
requires: [one-transvection-ternary-s0-lift-is-left-invertible, two-piece-left-inverses-are-corner-left-inverses, stable-finiteness-failure-refutes-surjunctivity]
artifacts:
  - research/artifacts/ternary-one-transvection-two-piece-lift-2026-09-12.md
---

## Why sufficient

1. **A one-sided unit of `S_-`.** `one-transvection-ternary-s0-lift-is-left-invertible` gives
   `v in P_(d1) S_- P_(d1)` with `v Y_h = P_(d1)`. `two-piece-left-inverses-are-corner-left-inverses`, with
   `P = P_(d0)`, `P' = P_(d1)` and `u1 = u0 h`, turns it into `c = (P_(d0) + v - P_(d0)[h]v)[u0^(-1)]` with
   `c a = 1`, where `a = u0 P_(d0) + u1 P_(d1)`.
2. **Not invertible.** `pi(a) = u0 s0 t0 + u1 s1 t1 = s00 t0 + s01 t1 = s0` (artifact Corollary A.1), and `s0` is
   not a unit of `L_(F_3)(1,2)`. So `a c != 1`.
3. **Padding.** `eps_+ = 1 - eps_-` is a central idempotent. Put `A = a + eps_+` and `B = c + eps_+` in
   `F_3[G]`. Then `B A = eps_- + eps_+ = 1` and `A B = ac + eps_+ != 1`, so `F_3[G]` is not directly finite.
4. **The criterion.** `stable-finiteness-failure-refutes-surjunctivity` at `k = F_3` and `n = 1` gives an
   injective, non-surjective linear cellular automaton on `F_3^G`.

The route is sound and its only open input is the corner claim. It is the direct stage-one form
`J_1(S_-) != 0` of `weakly-finite-reflection-ideal-detects-weakly-finite-images`, and needs no fullness,
state or rank statement.
