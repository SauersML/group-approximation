---
rg: 2
id: rounder-from-uniform-kernel-resolution
kind: route
title: Use the same amplifier's kernel resolution and local spectral bounds to exactify at constant cost
target: amplified-hamiltonian-has-a-constant-cost-rounder
requires: [amplifier-admits-a-uniform-local-kernel-resolution, kernel-resolutions-and-local-spectra-bound-rounder-cost]
artifacts:
  - research/artifacts/qpcp-kernel-resolution-2026-09-07.md
---

Apply the uniform-cost theorem to each NO output of the single specified
amplifier, using its supplied resolution, neighborhoods, and constants.
It gives an exact rounder with uniform cost at most `R/delta`. Recovery
may prepare a fixed retained-kernel vector for each measured feasible set.
This suffices for the existential rounder interface and its soundness
transfer; it does not establish the stronger physical port implementation
claim. The separate amplifier and YES-margin prerequisites of the QPCP
route must still hold for this same reduction.
