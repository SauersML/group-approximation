---
rg: 2
id: atlas-six-relator-l5-screen-proof
kind: route
title: Exhaust both marking parities in the natural GL5(2) permutation image
target: atlas-six-relator-l5-has-no-marked-pair
requires:
  - atlas-a8-index-91-to-496-reaches-standard-l5
artifacts:
  - experiments/atlas_six_relator_gl5_scan.py
  - experiments/atlas-six-relator-gl5-scan.json
---

The ambient classification makes every chart conjugate to the standard
block `GL4(2)` and proves that its normalizer is itself.  The outer
inverse-transpose marking is therefore tested separately.  In each parity
the exact internal GAP loop ranges the full faithful permutation group of
order `9999360`, evaluates the literal six words in order, and asserts that
the first-failure totals plus survivors equal the group order.  Both survivor
counts are zero, proving the target.
