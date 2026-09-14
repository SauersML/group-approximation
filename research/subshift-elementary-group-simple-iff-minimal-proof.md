---
rg: 2
id: subshift-elementary-group-simple-iff-minimal-proof
kind: route
title: Minimal gives simple by the subsystem sandwich; a proper subsystem gives a proper nontrivial kernel
target: subshift-elementary-group-simple-iff-minimal
requires: [aperiodic-subshift-el-normal-subgroups-are-sandwiched]
artifacts:
  - research/artifacts/sk-open-1-subsystem-normal-subgroups-2026-09-13-part1.md
---

If X is infinite and minimal:
- X has no periodic points, and its only closed invariant subsets are ∅ and X.
- By the sandwich, every normal subgroup N satisfies E_∅ = G ≤ N, or N ≤ ker π_X = 1.

If X is not minimal:
- Choose a closed invariant Y with ∅ ≠ Y ≠ X, and a nonempty clopen V disjoint from Y.
- Restriction of coefficients π_Y : EL_n(R_X) → EL_n(R_Y) is a homomorphism.
- Its kernel contains e_12(e_V) ≠ 1, and it is proper because π_Y(e_12(1)) = e_12(1) ≠ 1.

This direction uses no aperiodicity.
