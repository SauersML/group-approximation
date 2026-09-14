---
rg: 2
id: finitely-many-minimal-sets-el-normal-subgroups-proof
kind: route
title: The subsystem dictionary for finitely many minimal subsets, from the sandwich and restriction kernels off the minimal sets
target: finitely-many-minimal-sets-el-normal-subgroups-are-kernels
requires:
  - restriction-kernel-relative-elementary-off-minimal-sets
  - minimal-set-complement-ideal-is-ultramatricial
  - aperiodic-subshift-el-normal-subgroups-are-sandwiched
  - aperiodic-subshift-ring-ideals-are-invariant-open-sets
artifacts:
  - research/artifacts/sk-k2-recurrent-2026-09-13.md
---

Details: `research/artifacts/sk-k2-recurrent-2026-09-13.md` §4.
1. **No periodic points.** A periodic orbit would be a finite minimal subset. So `aperiodic-subshift-el-normal-subgroups-are-sandwiched` applies: every N ⊴ G has exactly one closed invariant Y with E_n(R_X,I_Y) ≤ N ≤ ker π_Y.
2. **Z.** Given Y, let Z be the union of the M_i not contained in Y. Minimal sets lie in Y or miss it, so Z is closed, invariant and disjoint from Y, and every minimal subset lies in Y ∪ Z.
3. **Kernels.** `restriction-kernel-relative-elementary-off-minimal-sets` gives ker π_Y = E_n(R_X,I_Y), so N = ker π_Y.
4. **Bijection.** ker π_Y determines I_Y = {r : e_12(r) ∈ ker π_Y}, hence Y (`aperiodic-subshift-ring-ideals-are-invariant-open-sets`). π_Y is onto because elementary generators lift.
5. **(b).** Y = ⋃M_i contains every minimal subset, so `minimal-set-complement-ideal-is-ultramatricial` makes ker π_Y = G ∩ GL_n(R_X,I_Y) locally finite. R_{⋃M_i} = ∏ R_{M_i}. Each EL_n(R_{M_i}) is infinite, finitely generated, simple, Kazhdan and LEF by the note's theorem for infinite minimal subshifts. □
