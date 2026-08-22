---
rg: 2
id: odd-spectral-sign-budget-proof
kind: route
title: Polarize the odd part and telescope negative anchor projections
target: odd-spectral-anchor-resets-have-monotone-sign-budget
requires:
  - spectral-cut-anchor-reset-pays-boundary-in-one-row
---

The polar unitary of the anchor-odd part on a positive `Y^2` spectral cut
anticommutes with the anchor and bijects its sign sectors.  The reset sets
the cut block of the anchor to `1`, deleting exactly the negative half.
Telescope traces through the decreasing negative projections; no
commutation between cuts from different iterations is required.
