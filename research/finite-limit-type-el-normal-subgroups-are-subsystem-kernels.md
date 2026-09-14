---
rg: 2
id: finite-limit-type-el-normal-subgroups-are-subsystem-kernels
kind: claim
title: If the limit set of a subshift is a finite union of infinite minimal subshifts, normal subgroups of EL_n(LC(X,F_2)⋊Z) are exactly restriction kernels
distinct_from:
  elementary-group-normal-subgroups-are-subsystem-kernels: that is the open conjecture for every aperiodic subshift; this proves it when the closure of the limit set is a finite union of minimal subshifts
artifacts:
  - research/artifacts/sk-k2-subsystems-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed)** via `finite-limit-type-el-normal-subgroups-proof`.

Setting:
- X ⊆ A^Z is a subshift, and cl L(X) = M_1 ∪ … ∪ M_s is a finite union of infinite minimal subshifts, where L(X) is the union of all α- and ω-limit sets.
- n ≥ 3 and G = EL_n(LC(X,F_2) ⋊ Z).

Conclusions:
- (a) Y ↦ ker(G → EL_n(R_Y)) is an inclusion-reversing bijection from closed invariant subsets of X onto normal subgroups of G, and G/ker π_Y ≅ EL_n(R_Y).
- (b) The kernel K onto M_1 ∪ … ∪ M_s is locally finite, and G/K ≅ ∏_i EL_n(R_{M_i}). So G is an extension of a locally finite group by a finite product of infinite simple Kazhdan LEF groups.

Example: a Sturmian subshift plus one orbit asymptotic to it on both sides gives exactly three normal subgroups.
