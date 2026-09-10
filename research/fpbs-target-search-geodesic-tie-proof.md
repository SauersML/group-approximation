---
rg: 2
id: fpbs-target-search-geodesic-tie-proof
kind: route
title: Count tied rectangle layers and show strict weighting follows decreasing-distance tips
target: fpbs-target-search-geodesic-tie-calibration
requires:
  - fpbs-unit-target-search-ellipse-bound
artifacts:
  - research/artifacts/fpbs/search-geometry.md
---

Section 3 confines unit-weight search to an all-open geodesic rectangle,
where insertion-order ties explore whole depth layers before meeting.
Their triangular vertex count gives the quadratic lower bound. For beta>1,
each forward geodesic step has priority strictly lower than every pending
ancestor candidate, so each side takes at most D open steps before meeting.
