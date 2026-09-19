---
rg: 2
id: parity-multicut-closes-gapless-generated-sector
kind: route
title: Apply the clipping dichotomy and pay the entire cut tree with balanced parity
target: balanced-overlay-gapless-adjoint-sector-rounding
requires:
  - bounded-low-gap-witness-gives-balanced-cut
  - low-gap-witness-spike-or-balanced-cut
  - small-trace-rank-one-quarantine
  - adjoint-parity-cone-lifts-to-loewner-order
  - common-cut-contraction-sign-has-complete-balanced-energy-ledger
  - block-adaptive-sparse-reset-is-cheap
  - uniform-generated-adjoint-gap-rounds-to-central-code
  - balanced-parity-multicut-boundary-is-summable
---

Use clipping/coarea on every low-gap generated-algebra corner.  Balanced
cuts are made literally reducing with the common compression/sign ledger;
spike supports are quarantined into rank-one atoms.  The Loewner
fundamental-cone estimate spreads each cut boundary uniformly over code
coordinates, so fixed-width parity rows and equality copies are repaired at
the same normalized cost.  The multicut theorem makes the entire recursive
boundary and spike budgets vanish and leaves only terminal blocks with gap
`lambda_0`.  Apply `uniform-generated-adjoint-gap-rounds-to-central-code`
there; `(BPM2)` makes its `epsilon/lambda_0` correction vanish.  Integrating
the terminal and quarantined blocks proves the gapless-sector rounding
claim.
