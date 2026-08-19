---
rg: 2
id: orbit-summed-extraction
kind: route
title: Orbit-summed whole-map extraction after same-orbit closure
target: common-self-map-law
requires: [same-orbit-closure, transition-equivariance]
artifacts:
  - notes/TRUE_EQUIVARIANT_TRANSITIONS_COARSEN_TO_WHOLE_MAPS.md
---

Claimed reduction (AGENDA 2026-08-14): once the raw/comb transition PVM is
equivariant under the named middle-root translations (transition-equivariance), pulling every
source-conditioned response PVM to one base block and orbit-summing gives an
exact whole-map PVM within `40ε` of the equivariance error, independently of
orbit size, response alphabet, and matrix dimension (whole-map-coarsening). Same-orbit
closure (same-orbit-closure) excludes the rectangular target enlargement that rectangular-escape
exposed, so the orbit-summed law lands on ONE source-sized paired label
space — exactly common-self-map-law.
