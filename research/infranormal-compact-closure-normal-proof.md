---
rg: 2
id: infranormal-compact-closure-normal-proof
kind: route
title: Reverse compact semigroup inclusions by recurrence
target: infranormal-compact-closure-normal
requires: []
artifacts:
  - notes/FALSE_COMPACT_BOGOLIUBOV_APPROXIMATION_FOR_KUN_THOM.md
---

For a compressor `t`, let `H` be the compact closure of `rho(Gamma)`.
Choose positive integers `n_j` with `rho(t)^(n_j)->1`.  The one-sided
inclusion implies
`rho(t)^(n_j-1) H rho(t)^(-(n_j-1)) <= H`; closedness and passage to the
limit give the reverse inclusion under `rho(t)^(-1)`.  Thus `rho(t)`
normalizes `H`.  The compressors generate `G`, proving normality.
