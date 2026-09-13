---
rg: 2
id: phase-zero-kernel-and-normal-generation-lower-mf-rank
kind: route
title: Embed the full high-rank return kernel, extract its phase-zero subgroup and normally generate the ambient transient kernel
target: short-period-free-low-rank-mf-radical-is-core-kernel
requires:
  - full-return-section-preserves-core-and-generates-kernel
  - subshift-mf-radical-is-the-locally-finite-core-kernel
  - clopen-return-towers-transfer-direct-finiteness-and-matrix-rank
artifacts:
  - research/artifacts/pestov91-return-core-full-low-rank-radical-2026-09-13.md
---

Section 3 embeds the return group at rank `nk>=4` into the first `k`
tower levels. Its invisible kernel contains every phase-zero placement
of a low-rank return-kernel element, even a rank-one unit. Normal
generation then kills the entire ambient kernel, and the LEF core
restriction gives the opposite inclusion.
