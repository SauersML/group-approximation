---
rg: 2
id: jacobson-two-braid-mixed-packet-gap
kind: claim
title: The marked Jacobson two-braid infimum is positive over arbitrary packet multiplicities
artifacts:
  - research/artifacts/jacobson-two-braid-reduction-2026-09-07.md
distinct_from:
  binary-jacobson-steinberg-head-root-is-mf-invisible: that concerns the full rank-five Jacobson group; this asks for a gap using only the smaller explicit joint two-cell presentation.
  binary-jacobson-joint-shortest-cells-have-a-finite-marked-model: that asks for one exact finite marked quotient; this asks for a uniform obstruction even to approximate finite-dimensional unitary models and would contradict that finite-model claim.
---

**OPEN.** Prove that `gamma>0` for the exact packet infimum defined in
`jacobson-two-braid-gap-characterizes-mark-collapse`, without any
Property-(T) input.

## Attempts

- The separated-factor class has maximum braid defect exactly two if
  the mark survives. This includes arbitrary head and tail modules on
  separate summands, even when the involution mixes those summands.
- Below defect two, general complex packets must have the four-group
  multiplicity table and marked rank `8k` proved in
  `jacobson-joint-cells-are-two-braids`. A 56-point packet satisfies
  these necessary constraints with `k=2`, so rank balance alone does
  not close this claim.
- The infimum still ranges over unbounded multiplicities of arbitrary
  representations where both factors act on the same summand. No
  positive lower bound for that remaining class has been proved.
