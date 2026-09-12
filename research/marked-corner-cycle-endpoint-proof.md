---
rg: 2
id: marked-corner-cycle-endpoint-proof
kind: route
title: Apply the robust BCS gap inside the common central-sign corner
target: marked-corner-cycle-needs-no-full-mass-concentration
requires:
  - corner-localized-non-ce-bcs-energy-gap
  - forbidden-weighted-type-carrier-coverage-is-rank-rounding
  - global-marked-type-cycle-selector-decoder
  - central-sign-bcs-energy-decoder-implies-nonhyperlinear
---

Exhaustivity `(MCN1)` identifies the marked forbidden mass `(FWC4)` with
`sum_c tr(F_cQ)`.  Rank trimming loses only `O(1/d)`.  Re-run the proof of
`(GTC6)` with this marked quantity in place of the full-space
`E_forbid`; only `(GTC4)`, type orthogonality, and the cyclic quarter-trace
floor are used.

The localized BCS inequality `(CLG1)` on `Q` supplies `(MCN3)`.  The base
rows or the cycle actuator therefore pay a fixed multiple of `tr(Q)`.
Central-sign exactification makes `tr(Q)->1/2` in canonical microstates, and
the abstract central-sign terminal theorem gives nonhyperlinearity.
