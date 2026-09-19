---
rg: 2
id: nv-periodic-groups-via-graded-renormalization
kind: route
title: A graded height-3 renormalization of an element of nV puts Nekrashevych's ternary periodic fragmentation into nV
target: brin-thompson-groups-contain-infinite-periodic-groups
requires:
  - some-nv-element-has-a-graded-height-3-renormalization
  - graded-renormalization-gives-ternary-toeplitz-factor
---

**Route (conditional; the input is OPEN).** Lane bh-free-01.

`some-nv-element-has-a-graded-height-3-renormalization` supplies `g ∈ nV`, a clopen `A`, and data
satisfying (R1)–(R4). Item 3 of `graded-renormalization-gives-ternary-toeplitz-factor` then embeds the ternary
fragmentation `G = ⟨h_1, h_2, b⟩` in `nV`. `G` is infinite, finitely generated and periodic, which is the
target.

This refines `nv-periodic-groups-via-schreier-subshift-factors`: the needed factor map is produced from a
property of a single element (a colouring cycled by a renormalization), with no factor map given in advance.
