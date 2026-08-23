---
rg: 2
id: atlas-six-relator-sp6-screen-proof
kind: route
title: Exhaust the unique orthogonal A8 class in one exact Sp6(2) loop
target: atlas-six-relator-sp6-has-no-marked-pair
requires: []
artifacts:
  - experiments/atlas_six_relator_sp6_scan.py
  - experiments/atlas-six-relator-sp6-scan.json
---

Construct `Sp_6(2)`, enumerate its maximal `S8` subgroups, and verify that
their derived `A8` subgroups form one conjugacy class.  Fix one exact marked
`GL_4(2)~=A8` chart.  The one internal GAP loop ranges the relative
conjugator through all `1451520` elements and evaluates the six literal
free-product words in order.  The normalizer has order `40320`, so its
noninner coset includes the outer marking parity.  The first-failure counts
sum to the ambient group order and the survivor count is zero, proving the
target.
