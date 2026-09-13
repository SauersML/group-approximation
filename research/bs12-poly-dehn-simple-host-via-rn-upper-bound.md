---
rg: 2
id: bs12-poly-dehn-simple-host-via-rn-upper-bound
kind: route
title: Bound the Dehn function of the Röver–Nekrashevych envelope over Cornulier–Tessera's host
target: bs12-embeds-in-fp-simple-group-with-polynomial-dehn-function
requires:
  - bs12-lies-in-fp-simple-rn-envelope-of-quadratic-dehn-host
  - rover-nekrashevych-dehn-polynomial-in-host-and-vd
  - higman-thompson-vd-has-polynomial-dehn-function
artifacts:
  - research/artifacts/solve-bh-poly-dehn-2026-09-13.md
---

Let `Gamma_2` be Cornulier–Tessera's host and `S = [V_10(Gamma_2),
V_10(Gamma_2)]`. By `bs12-lies-in-fp-simple-rn-envelope-of-quadratic-dehn-host`:
- `S` is finitely presented and simple;
- `BS(1,2) <= S`;
- `δ_S ≃ δ_(V_10(Gamma_2))`;
- `Gamma_2` has quadratic Dehn function and satisfies Zaremsky's four hypotheses
  on the 10-ary tree.

By `higman-thompson-vd-has-polynomial-dehn-function` at `d = 10`,
`δ_(V_10)` is polynomially bounded. By
`rover-nekrashevych-dehn-polynomial-in-host-and-vd` with `G = Gamma_2` and
`d = 10`, `δ_(V_10(Gamma_2))` is polynomially bounded. So `δ_S` is polynomially
bounded, and `S` witnesses the target.
