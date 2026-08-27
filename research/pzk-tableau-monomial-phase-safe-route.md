---
rg: 2
id: pzk-tableau-monomial-phase-safe-route
kind: route
title: Use the private-S5 rational tableau as a narrowed monomial compiler source
target: phase-safe-toric-gap-game-exists
requires:
  - lin-pzk-tableau-rational-qc-not-qa-correlation
  - pzk-tableau-private-s5-gauge-normal-form
  - finite-phase-monomial-game-algebra-dictionary
  - pzk-tableau-gap-full-corner-monomial-realization
  - monomial-gap-phase-safe-toric-groupification
artifacts:
  - research/artifacts/mastel-slofstra-tableau-compiler-audit-2026-08-23.md
---

The Lin--Mastel--Slofstra construction supplies one fixed separated source
whose perfect trace is rational and whose only cross-tableau variables are
shared Boolean shares.  Solve
`pzk-tableau-gap-full-corner-monomial-realization` to encode the complete
universal source algebra, not only its selected trace, as a finite-phase
monomial matrix-pair algebra.  The exact finite-phase dictionary then retains
the commuting/`R^omega` separation.

Finally apply `monomial-gap-phase-safe-toric-groupification`.  The two open
requirements are independent: the first is a full-corner square completion,
while the second must prove survival of the scalar Fourier phase under normal
closure.  Rational marginals and private `S5` rows solve neither one by
themselves.
