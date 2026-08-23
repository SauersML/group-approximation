---
rg: 2
id: terminal-pinching-and-spike-budget-imply-balanced-multicut
kind: route
title: Replace recursive boundary accounting by one terminal pinching displacement
target: balanced-parity-multicut-boundary-is-summable
requires:
  - nested-common-cuts-have-exact-pythagorean-boundary-ledger
  - adaptive-spike-quarantines-have-summable-trace
  - low-gap-cut-and-spike-dichotomy-holds-for-contractions
  - common-cut-contraction-sign-has-complete-balanced-energy-ledger
  - terminal-common-pinching-displacement-vanishes
---

Choose the adaptive geometric spike budget with `eta=o(1)`.  It gives the
second assertion of `(BPM1)` and makes all rank-one quarantine costs vanish.
On the complement, use the terminal PVM supplied by
`terminal-common-pinching-displacement-vanishes`.  Exact cut Pythagoras
identifies the first sum in `(BPM1)` with its single terminal displacement,
which is `o(1)`.  Keep contractions throughout the nested tree and invoke
the common compression/sign ledger only once on the terminal partition;
all approximate parity and complete-pair damage is then charged to that
same displacement rather than once per level.  The terminal claim supplies
the gap and scale assertions `(BPM2)`.
