---
rg: 2
id: rowwise-hecke-crt-from-affine-frobenius-packets
kind: route
title: Store every context in an almost-full Frobenius block and solve shared involutions variablewise
target: rowwise-hecke-crt-certificate-for-nonce-bcs
requires:
  - affine-frobenius-packets-solve-local-row-mask-storage
  - affine-frobenius-hecke-crt-shared-involution-interpolation
---

Choose `p` so large that the sum of all weighted `1/p` local deficits leaves
strict room below the fixed game gap.  The Frobenius packets realize the one
global PVM for every context and every prescribed rational local marginal.
The interpolation claim adds one global involution per variable and private
large right-ideal masks without changing those PVMs.  These are exactly
`(HCRT1)--(HCRT2)`.

