---
rg: 2
id: elementary-group-normal-subgroups-are-subsystem-kernels
kind: claim
title: Normal subgroups of EL_n over an aperiodic subshift crossed product are exactly the restriction kernels to subsystems
---

**OPEN.** Let X ⊆ A^Z be a subshift without periodic points and n ≥ 3. Put G_X = EL_n(LC(X,F_2) ⋊ Z).

Conjecture:
- Y ↦ ker(G_X → G_Y) is an inclusion-reversing bijection from closed invariant subsets of X onto normal subgroups of G_X.
- Every quotient of G_X is isomorphic to some G_Y.

Status:
- Established: the sandwich E_Y ≤ N ≤ ker π_Y (`aperiodic-subshift-el-normal-subgroups-are-sandwiched`).
- The simplicity criterion is the special case in `subshift-elementary-group-simple-iff-infinite-minimal`.
- Open: the K_2 layer (`aperiodic-subshift-ring-unstable-k2-vanishes`).
- Established for finite limit type (unreviewed). If the closure of the limit set of X is a finite union of infinite minimal subshifts, the dictionary holds, and the kernel onto the limit set is locally finite (`finite-limit-type-el-normal-subgroups-are-subsystem-kernels`).
- The K_2 layer needs only surjectivity of K_2(n,R_X) → K_2(n,R_Y) (`subshift-restriction-kernel-is-relative-elementary`).
