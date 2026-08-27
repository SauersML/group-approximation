---
rg: 2
id: fanizza-wandering-exit-closes-triangle-cell
kind: route
title: Exclude finite Fanizza microstates by overflowing the wandering mirror exit
target: single-triangle-trace-cyclic-return-cell
requires:
  - fanizza-mirror-exit-wanders-through-toeplitz-cells
  - wandering-complement-contractions-pay-fanizza-mirror
---

Apply `(WCM4)` to the decoded data `(FMW1)--(FMW3)`.  It gives `(FMW4)`,
contradicting `tr(H)=1/8+o(1)` once the presentation defect is sufficiently
small.  Thus the cell has no vanishing-defect finite microstate sequence;
below the resulting threshold the finite return estimates required by
`single-triangle-trace-cyclic-return-cell` hold vacuously, exactly as in the
established one-sided rank-floor route.

The exact countably amplified marked representation extends because its
complement exit `A` is zero.  No fixed group-algebra proper-return identity
has been added: the contradiction uses the number of decoded wandering
coordinates in a finite matrix and finite trace capacity.  Hence the marked
word remains nonzero and the regular-trace firewall is respected.
