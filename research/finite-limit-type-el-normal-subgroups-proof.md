---
rg: 2
id: finite-limit-type-el-normal-subgroups-proof
kind: route
title: Sandwich every normal subgroup, then close the congruence layer with Z = the minimal components outside Y
target: finite-limit-type-el-normal-subgroups-are-subsystem-kernels
requires:
  - subshift-restriction-kernel-is-relative-elementary
  - biasymptotic-subshift-complement-ideal-is-ultramatricial
  - ultramatricial-ideals-have-elementary-congruence-kernels
  - aperiodic-subshift-el-normal-subgroups-are-sandwiched
  - aperiodic-subshift-ring-ideals-are-invariant-open-sets
artifacts:
  - research/artifacts/sk-k2-subsystems-2026-09-13-part1.md
---

The full proof is Corollary E in the artifact.
- **Aperiodic.** A periodic orbit is its own limit set, so it would be a finite minimal component of cl L(X). So X is aperiodic, and the sandwich gives every N ⊴ G a unique Y with E_n(R_X,I_Y) ≤ N ≤ ker π_Y.
- **Choose Z.** Let Z be the union of the M_i not contained in Y. Minimal sets are disjoint from each other and either lie in Y or miss it, so Z is closed, invariant and disjoint from Y. Limit sets of points outside Y ∪ Z are closed invariant subsets of ⋃M_i, so they lie in Y ∪ Z.
- **Close the layer.** By `subshift-restriction-kernel-is-relative-elementary`, ker π_Y = E_n(R_X,I_Y). So N = ker π_Y.
- **Bijection.** ker π_Y determines I_Y, hence Y, by the ideal classification. π_Y is onto because elementary generators lift.
- **(b).** For Y = ⋃M_i take Z = ∅. The kernel lies in GL_n(R_X,I_Y), which is locally finite. Also R_{⋃M_i} = ∏R_{M_i}. ∎
