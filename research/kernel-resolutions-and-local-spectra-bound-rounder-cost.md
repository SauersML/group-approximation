---
rg: 2
id: kernel-resolutions-and-local-spectra-bound-rounder-cost
kind: claim
title: A feasible kernel resolution and a uniform positive local spectrum give a constant-cost rounder
artifacts:
  - research/artifacts/qpcp-kernel-resolution-2026-09-07.md
  - scripts/check_qpcp_kernel_resolution.py
  - research/artifacts/qpcp-kernel-resolution-replay-2026-09-07.json
distinct_from:
  finite-syndrome-cost-is-a-kernel-support-cone-test: that characterizes finite cost per instance; this supplies a uniform quantitative bound across a family and a finite local term collection criterion for the needed spectrum.
  bounded-overlap-syndrome-energy-accounting: that sums supplied charges; this derives those charges from support and the nonzero spectrum of each local neighborhood sum.
---

Suppose a family has feasible resolutions `I=sum_S T_S` with
`ran T_S subset intersection_(a in S) ran A_a`, and
`A_a>=delta P_(ran A_a)` for one uniform `delta>0`. If neighborhood
occurrence is at most `R`, an unrestricted exact rounder has cost at most
`R/delta`.

Such a uniform local spectral bound follows from bounded local dimension,
term locality, and neighborhood cardinality, together with a fixed finite
collection of local term matrices with no varying weights. Constant local
dimension alone does not imply the finite-collection hypothesis. Neither
the spectral bound nor finite-dimensional existence constructs the required
resolutions for an amplifier.
