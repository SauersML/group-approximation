---
rg: 2
id: nonhyperlinear-via-pi-degree-reservoir-lock
kind: route
title: Lock the atlas multiplicity reservoir and separate its label degree by one fixed PI evaluation
target: non-hyperlinear-group
requires:
  - leavitt-regular-atlas-hyperlinearity-criterion
  - fixed-pi-degree-fingerprints-packet-label-factor
  - common-corner-mutual-bicommutant-extraction
artifacts:
  - research/artifacts/nonhyperlinear-breakout-portfolio-2026-08-21.md
---

Assume the explicit regular-atlas Leavitt group were hyperlinear and extract
the canonical relative-unitary matrix microstates supplied by
`leavitt-regular-atlas-hyperlinearity-criterion`.  The mutual-bicommutant
claim makes the physical label and reservoir factors word-visible on one
positive-density corner, excluding their exchange in `rectangular-escape`.
The fixed-PI claim then evaluates `s_(2r)` as `o(1)` on the source label factor
and at least `sqrt(alpha) kappa_r-o(1)` on the transported full target factor,
while the closed word transport makes the two evaluations `o(1)` apart.
Contradiction.  This route records the memo interface only; its two open
packet claims belong to the separately assigned BCS/Steinberg team.

