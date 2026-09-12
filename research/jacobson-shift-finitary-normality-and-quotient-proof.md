---
rg: 2
id: jacobson-shift-finitary-normality-and-quotient-proof
kind: route
title: Telescope the tail actions and eliminate the normally generated finite packets
target: jacobson-shift-head-generates-normal-finitary-kernel
requires:
  - jacobson-shift-has-full-finite-linear-intervals
artifacts:
  - research/artifacts/jacobson-recursive-packets-generate-finitary-linear-kernel-2026-09-08.md
---

Finite intervals give the faithful locally finite union. Stable-letter
conjugation shifts the intervals. Tail factorization expresses `P_0`
on each packet by finitely many head factors and a commuting residual
tail. The analogous expression for the staggered involution uses
finitely many pure swaps and the next boundary, whose conjugation is
already contained in the adjacent finite linear group. These facts
prove normality for all positive and negative interval positions.

Conjugates of the marked transvection generate every finite packet,
so their union is exactly its normal closure. For simplicity, a
commutator of any nonidentity finitary element with a transvection
to a fresh coordinate is a nonidentity transvection. Its finite
conjugates generate the whole union.

Killing this normal closure kills `K` and `C_0`. The finite factors
reduce to two copies of `GL_3(F_2)` with common `K_P`; the two
mixed words specialize to those in the claim. All remaining stable
equations make `t` central. Reverse assignments verify the exact
quotient presentation. Sections 6--7 contain the details.
