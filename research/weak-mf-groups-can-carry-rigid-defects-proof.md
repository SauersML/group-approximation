---
rg: 2
id: weak-mf-groups-can-carry-rigid-defects-proof
kind: route
title: Normal forms in the finite-lamp amalgam keep the transported lamp moving
target: weak-mf-groups-can-carry-rigid-defects
requires: [symmetric-double-weak-mf, kun-thom-nonsofic-wreath]
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
---

Theorem E (`kun-thom-nonsofic-wreath`) gives a residually finite Kazhdan `G`
and an infranormal, non-normal Kazhdan `Gamma`. `symmetric-double-weak-mf`
makes `H_K = G *_Gamma (Gamma x K)` operator MF.

Defect computation, with `A = G`, `B = Gamma x K`, `C = Gamma`:

1. A strict compressor `t` exists, since `Gamma` is not normal and compressors
   generate `G`.
2. `k in K \ {1}` commutes with `Gamma`.
3. `t k t^-1` is a reduced word of type `(A\C)(B\C)(A\C)`.
4. Reduced words `a_1 b a_2 = a'_1 b' a'_2` require `a'_1 in a_1 C`.
5. `gamma (t k t^-1) gamma^-1` has first letter `gamma t`, so equality would
   force `t^-1 gamma t in Gamma`. That fails for
   `gamma in Gamma \ t Gamma t^-1`.
6. So `[t k t^-1, gamma] != 1`.

Artifact Section 6.
