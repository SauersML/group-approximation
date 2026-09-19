---
rg: 2
id: commuting-lamp-mf-detects-defect
kind: route
title: Detect the unsquared defect through the commuting-lamp quotient
target: unsquared-defect-mf-visible
requires: [commuting-lamp-quotient-mf, commuting-lamp-defect-survives]
artifacts: [non_mf_groups_exist.tex]
---

## Why sufficient

The map `E -> W/<zeta>` kills `w` but, by
`commuting-lamp-defect-survives`, does not kill `u`.  If the target is MF,
compose this map with a faithful norm-matrix-corona representation of the
target.  The resulting corona representation of `E` detects `u`, so `u` is
not in the intersection of all corona kernels.
