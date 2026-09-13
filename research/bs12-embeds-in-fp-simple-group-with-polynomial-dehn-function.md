---
rg: 2
id: bs12-embeds-in-fp-simple-group-with-polynomial-dehn-function
kind: claim
title: BS(1,2) embeds in a finitely presented simple group with polynomially bounded Dehn function
distinct_from:
  np-word-problem-groups-embed-in-fp-simple-polynomial-dehn-groups: that asks for every finitely generated input with word problem in NP; this is its BS(1,2) test case.
  bs12-lies-in-fp-simple-rn-envelope-of-quadratic-dehn-host: that gives a finitely presented simple group containing BS(1,2) with no upper bound on its Dehn function; this asks for a polynomial upper bound.
artifacts:
  - research/artifacts/solve-bh-poly-dehn-2026-09-13.md
---

**OPEN.** There is a finitely presented simple group `S` with polynomially
bounded Dehn function and `BS(1,2) <= S`.

**Status (2026-09-13).**
- The generator `a` of `BS(1,2)` is exponentially distorted.
- `T`, `T_n`, `V`, `VA` and CAT(0) simple lattices can't contain it (Attempts 3–4
  of the root).
- Twisted Brin–Thompson envelopes can't have polynomial Dehn function unless
  NP = coNP (`twisted-btb-groups-poly-dehn-only-if-np-eq-conp`).
- The one candidate on main is `S = [V_10(Gamma_2), V_10(Gamma_2)]` over
  Cornulier–Tessera's quadratic host
  (`bs12-lies-in-fp-simple-rn-envelope-of-quadratic-dehn-host`, ESTABLISHED).
  Its Dehn function is at least quadratic, with no known upper bound.

**Route.** `bs12-poly-dehn-simple-host-via-rn-upper-bound` reduces this claim to
two upper bounds, both open:
- `rover-nekrashevych-dehn-polynomial-in-host-and-vd`;
- `higman-thompson-vd-has-polynomial-dehn-function`.
