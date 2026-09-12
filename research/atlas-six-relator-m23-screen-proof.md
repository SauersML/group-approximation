---
rg: 2
id: atlas-six-relator-m23-screen-proof
kind: route
title: Exhaust both marking parities in the four maximal-A8 double cosets of M23
target: atlas-six-relator-m23-has-no-marked-pair
requires:
  - atlas-a4-m23-packet-double-coset-screen
artifacts:
  - experiments/atlas_six_relator_m23_scan.py
  - experiments/atlas-six-relator-m23-scan.json
---

The established ATLAS construction proves that the maximal `A8` is one
class and self-normalizing.  Its four double cosets partition `M23`; the
attached replay checks their sizes and scans each exactly in the inner and
graph marking parities.  Every cell has zero survivor count, and each
first-failure census sums to the cell size.  This exhausts all marked pairs.
