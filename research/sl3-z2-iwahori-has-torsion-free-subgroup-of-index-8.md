---
rg: 2
id: sl3-z2-iwahori-has-torsion-free-subgroup-of-index-8
kind: claim
title: The pro-2 Iwahori subgroup of SL_3(Z_2) has a torsion-free open subgroup of index 8
distinct_from:
  sl3-z2-iwahori-index-8-torsion-free-misses-level-4: that is the established census showing such a subgroup cannot contain the level-4 kernel; this asks whether one exists at all.
  sl3z-satisfies-strong-atiyah: that is the Strong Atiyah statement for SL_3(Z); this is the finite 2-adic group-theoretic input which implies it.
refuted_by:
  - sl3-zp-torsion-free-open-subgroups-have-index-divisible-by-48
artifacts:
  - research/artifacts/strong-atiyah-kazhdan-groups-2026-09-12.md
---

**REFUTED** (2026-09-12) by
`sl3-zp-torsion-free-open-subgroups-have-index-divisible-by-48`, through an
exhaustive mod-16 search.

Let `I <= SL_3(Z_2)` be the preimage of the upper unitriangular group
of `SL_3(F_2)`, so `[SL_3(Z_2):I] = 21`. The claim: some open subgroup `W <= I` of
index 8 contains no element of finite order. Equivalently, `SL_3(Z_2)` has a
torsion-free open subgroup of index 168.

Index 8 would be the minimum, since `I` contains a conjugate of the dihedral
group of order 8 in `SL_3(Z)`. Every index-8 subgroup contains
`K_4 = ker(SL_3(Z_2) -> SL_3(Z/16))`, by the Frattini chain in the artifact. So the
question is finite: an index-8 subgroup of `I/K_4`, of order `2^27`, containing
no image of an involution. There are two involution classes over `Z_2`,
`diag(1,-1,-1)` and `[[0,1],[1,0]] + (-1)`.

## Attempts

1. **Subgroups containing the level-4 kernel.** Excluded
   (`sl3-z2-iwahori-index-8-torsion-free-misses-level-4`). No avoiding subspace
   of codimension 2 exists, and none of codimension 3 is normalized by an order-8
   subgroup.
2. **Global Frattini refutation.** Every index-8 subgroup contains
   `Phi^3(I)`, which lies in `K_2` and so has no involutions. No quick
   refutation.
3. **Exhaustive pc-group search, done.** A GAP search on MSI (sbatch 556104,
   `experiments/strong-atiyah-sl3z/iwahori_index8_search.{g,out}`) went through
   all 7 maximal subgroups of `I/K_4` and all 69 second-level subgroups. It
   decided the last step by linear algebra over `M''/Phi(M'')`, against the
   27648 images of involutions. No torsion-free index-8 subgroup exists. The
   claim is false.
