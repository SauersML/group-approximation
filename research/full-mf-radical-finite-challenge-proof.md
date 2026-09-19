---
rg: 2
id: full-mf-radical-finite-challenge-proof
kind: route
title: Interpret the finite challenge as a nontrivial quotient of the saturated group
target: full-mf-radical-finite-challenge-cylinder
requires: [defect-saturation-full-mf-radical]
artifacts:
  - research/artifacts/hyperlinear-to-mf-saturation-compiler-2026-08-22.md
  - notes/TORSION_FREE_SATURATION_DIRECT_ROUTE_2026-08-14.md
  - GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean
---

## Proof

The finite relations `R` make every marked group in the cylinder a quotient
of `Q`; the inequation `v != 1` makes that quotient nontrivial.  Full MF
residual passes through surjections by
`coronaMFResidual_eq_top_of_surjective` and
`DefectRoutingData.quotient_normMFResidual_eq_top`, so every such marked
quotient has full MF residual and is non-MF.

The conditions `r=1` for `r in R` and `v != 1` depend on finitely many words,
so they are clopen cylinder conditions in the marked-group topology.  The
group `Q` itself is a point of the cylinder, proving nonemptiness.

This is the marked challenge recorded in
`notes/TORSION_FREE_SATURATION_DIRECT_ROUTE_2026-08-14.md` §§5--6, now
factored through the general saturation compiler rather than through a
central sign.
