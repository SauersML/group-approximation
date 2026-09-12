---
rg: 2
id: atlas-six-relator-hs-screen-proof
kind: route
title: Exhaust the five S8 double cosets of HS with the literal six words
target: atlas-six-relator-hs-has-no-marked-pair
requires:
  - atlas-six-relator-next-simple-target-is-hs
artifacts:
  - experiments/atlas_six_relator_hs_scan.py
  - experiments/atlas-six-relator-hs-scan.json
---

Construct the official `HS`, its maximal `S8`, and the derived `A8`.  GAP
computes the five exact `S8` double cosets.  The one internal loop evaluates
the six words on every element of each cell and records the first failure;
each cell's counts plus survivors equal its size.  The normalizer contains
both marking parities.  Every cell has zero final survivors, proving the
target.
