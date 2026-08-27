---
rg: 2
id: tree-localization-gives-site-noise-bridge
kind: route
title: Specialize the HS-to-site-noise bridge to conjugate tree leaves
target: clifford-hs-defect-becomes-adversarial-site-noise
requires:
  - nekrashevych-clifford-sign-tape
  - uniform-relative-clifford-tape-cell
  - tree-transitive-site-noise-localization
  - bgv-adversarial-fault-tolerance
---

The tree claim supplies a coherent tensor factorization away from the bad
leaves and bounds their fraction by the global relator energy.  Choose the
fixed local threshold below the relative-cell repair radius.  For sufficiently
small `E`, `(TSN1)` lies below the BGV adversarial correction radius, including
for coherent errors.  The recursive logical word retains the marked floor, so
the tensor realization, bad-site set, and function `F(n,E)` required by the
target all follow with constants independent of `n`.
