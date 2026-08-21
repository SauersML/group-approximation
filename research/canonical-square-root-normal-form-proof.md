---
rg: 2
id: canonical-square-root-normal-form-proof
kind: route
title: Retain the regular character through projection dilation and block rounding
target: canonical-iwahori-failure-is-a-regular-square-root-odd-mode
requires:
  - iwahori-transfer-reduces-to-square-root-block-mixing
  - iwahori-transfer-failure-has-two-positive-density-blocks
  - stable-representation-block-rounding
---

The projection dilation and stable block rounding perturb only fixed vertex
generator words by `o(1)`, so every fixed amalgam normal form retains its
canonical trace limit.  The general square-root reduction then supplies
`(CRS2)--(CRS3)` and the matched central edge word, while the density lemma
retains both physical blocks.  The odd/even identities are the exact
two-involution calculation in `(MSX3)--(MSX4)`.
