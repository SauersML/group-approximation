---
rg: 2
id: sofic-fp-pi2-completeness-from-sofic-safe-compiler
kind: route
title: Upper bound plus a sofic-safe compiler seeded by the finitely presented nonsofic group
target: sofic-recognition-finite-presentations-is-pi2-complete
requires:
  - sofic-safe-finite-presentation-compiler
  - sofic-recognition-has-a-pi2-upper-bound
  - finitely-presented-nonsofic-group-exists
---

## Why sufficient

The compiler gives `INF <=_m SOFIC_fp` (soficity on `INF`; on `FIN` the
output contains the nonsofic seed and soficity is hereditary), so
`SOFIC_fp` is `Pi^0_2`-hard and `NONSOFIC_fp` is `Sigma^0_2`-hard.
Membership is the permutation certificate.  Hardness plus membership is
completeness.
