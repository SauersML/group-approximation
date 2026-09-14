---
rg: 2
id: linear-scale-rank-conservation-does-not-kill-defects
kind: claim
title: Linear-scale rank conservation is compatible with a nontrivial compression defect of a Kazhdan subgroup
distinct_from:
  rank-ultraproduct-compressors-conserve-fixed-right-ideals: that is the conservation theorem for fixed right ideals; this shows its conclusions do not force compression defects to vanish.
  f2-linear-sofic-groups-kill-rigid-compression-defects: that is the open rank-row criterion, which assumes property (T) of the compressor group; this shows any proof of it must use that hypothesis below linear scale.
  sofic-groups-kill-rigid-compression-defects: that is the established Hamming criterion with property (T) of both groups; this uses the same sharpness witness to calibrate the rank metric's linear-scale layer.
artifacts:
  - research/artifacts/rank-row-compression-audit-2026-09-12.md
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
---

**ESTABLISHED.** Let `E` be the literal finitely presented group of
`non_mf_groups_exist.tex`. It is sofic, hence linear sofic over every field. Its
affine base `Gamma` is Kazhdan, with the doubling compressor `t`, some `c` in
`C_E(Gamma)` and `v_1` in `Gamma`, and

    u = [t c t^-1, v_1] != 1.

Fix any field `k` and any injective `sigma : E -> M^x` into a rank ultraproduct over
`k`. Every conclusion of `rank-ultraproduct-compressors-conserve-fixed-right-ideals`
holds for `Gamma <= <Gamma, t>`, in every tensor degree, and `sigma(u) != 1`.

So conservation of fixed right ideals in every degree does not imply triviality of
compression defects once property (T) of the compressor group is dropped. The
conservation theorem uses no property (T) at all. A proof of
`f2-linear-sofic-groups-kill-rigid-compression-defects` must therefore use property (T)
of the compressor group below linear scale, as the Hamming row does (ladder artifact
Theorem 4).
