---
rg: 2
id: finitely-many-minimal-sets-el-normal-subgroups-are-kernels
kind: claim
title: If a subshift has finitely many minimal subsets, all infinite, the normal subgroups of EL_n over its crossed product are exactly the restriction kernels to closed invariant subsets
distinct_from:
  finite-limit-type-el-normal-subgroups-are-subsystem-kernels: that needs the closure of the limit set of X to be a finite union of infinite minimal subshifts; this needs only finitely many minimal subsets, all infinite, which covers orbit closures of recurrent points where the limit set is all of X
artifacts:
  - research/artifacts/sk-k2-recurrent-2026-09-13.md
---

**ESTABLISHED (unreviewed)** via `finitely-many-minimal-sets-el-normal-subgroups-proof`.

Let X ⊆ A^Z be a subshift whose minimal subsets M_1, …, M_s are finitely many and all infinite. Let n ≥ 3, R_X = LC(X,F_2) ⋊ Z and G = EL_n(R_X).
- (a) Y ↦ ker(G → EL_n(R_Y)) is an inclusion-reversing bijection from the closed invariant subsets of X onto the normal subgroups of G, and every quotient of G is some EL_n(R_Y).
- (b) The kernel onto M_1 ∪ … ∪ M_s is locally finite, and the quotient is ∏_i EL_n(R_{M_i}), a finite product of infinite, finitely generated, simple Kazhdan LEF groups.

This settles `elementary-group-normal-subgroups-are-subsystem-kernels` for this class, which includes `recurrent-orbit-closure-with-unique-sturmian-minimal-set`.

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part4.md`):** PASS (§4); conditional on `aperiodic-subshift-el-normal-subgroups-are-sandwiched` and `aperiodic-subshift-ring-ideals-are-invariant-open-sets`.
