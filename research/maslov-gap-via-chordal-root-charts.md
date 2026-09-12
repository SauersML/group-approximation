---
rg: 2
id: maslov-gap-via-chordal-root-charts
kind: route
title: Exactify chordal root charts and charge the remaining Maslov cycle
target: maslov-mod3-projective-defect-gap
requires:
  - chordal-abelian-graph-products-hs-stable
  - c2-root-chart-maslov-holonomy-gap
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
---

Start with an `alpha`- or `alpha^2`-projective almost representation of the
chosen `C2` root presentation.  The chordal graph-product theorem exactifies
each commuting-root chart in the same dimension.  The synchronization and
cocycle localization asserted by `c2-root-chart-maslov-holonomy-gap` then
move all remaining projective curvature to a bounded non-chordal cycle.
Its positive HS energy lower bound contradicts arbitrarily small projective
presentation defect.  The same argument applies to the inverse multiplier,
proving the two-sector gap.
