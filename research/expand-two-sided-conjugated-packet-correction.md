---
rg: 2
id: expand-two-sided-conjugated-packet-correction
kind: route
title: Use both fixed-factor obstructions and expand the bilinear packet correction
target: both-rank-three-factors-must-be-packet-corrected
requires:
  - leavitt-rank-three-lift-has-no-one-sided-inverse
  - compressed-s-rank-three-lift-has-no-one-sided-inverse
  - single-conjugated-s3-packet-correction-equation
artifacts:
  - research/artifacts/one-nonnormal-packet-corner-correction-2026-08-21.md
---

If only `A` changes, the fixed `B` acquires a left inverse; if only `B`
changes, the fixed `A` acquires a right inverse.  Both are impossible by the
first two prerequisites.  Expanding the product with both packets and using
`AB=e+Delta` gives the displayed bilinear equation.  Evaluation kills both
packets, so any solution retains the nonidentity reverse image.
