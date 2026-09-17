---
rg: 2
id: fpbs-oblivious-certificates-never-localize-proof
kind: route
title: Charge each infinite-order label its forced crossing density times its absence-weighted cycle weight
target: fpbs-oblivious-certificates-never-localize
requires:
  - fpbs-relative-cycle-diagonal-absence-split
  - fpbs-graphing-cost-betti-cycle-dimension-identity
artifacts:
  - research/artifacts/fpbs/docs/oblivious-occupancy-localization-obstruction.md
---

Sections 2--5. By invariance the weighted boundary is the sum over
labels of the integral of the crossing s-edge diagonal of K. By the
absence split that diagonal is at least (1-p_s) rho_s. An infinite-order
label crosses on a set of measure at least 1/M, since M+1 consecutive
points of its line cannot share a block. For the uniform constant: the
cost--Betti identity gives sum rho_s = |S|-1, and the star chain gives
rho_s <= 1-1/(2|S|). At most one label has p_s>=2/3 when c<4/3, and
|S|>=2, so D>=1/12 and the weighted boundary is at least 2*4*(1/12)=2/3.
