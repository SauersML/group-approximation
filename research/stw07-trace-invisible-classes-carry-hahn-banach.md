---
rg: 2
id: stw07-trace-invisible-classes-carry-hahn-banach
kind: claim
title: Stabilized unitization makes every K_0-class trace-invisible without changing whether it is killed
distinct_from:
  stw07-bk-reduces-to-stable-character-kernels: that transfers quasidiagonality and stable finiteness to the stabilized unitization; this transfers the K_0-Hahn-Banach property at one class.
  k0-hahn-banach-for-boundary-singular-classes: that is the open boundary-class statement; this is the established fact that the boundary statement already contains the universal problem.
artifacts:
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
---

**ESTABLISHED.**  Let `A` be separable, nuclear and quasidiagonal, let
`x in K_0(A)`, and put `E = (A tensor K)~` with character `chi`.  Then:

1. `E` is separable, unital, nuclear and quasidiagonal; `chi` is its unique
   tracial state, and it is quasidiagonal;
2. `x` is singular in `K_0(A)` iff it is singular in `K_0(E)`, and
   `chi^(x) = 0`, with image `0` in `K_0(E/ker chi) = K_0(C)`;
3. `x` is killed by a faithful model of `A` iff it is killed by a faithful
   model of `E`.

Consequently the boundary statement `k0-hahn-banach-for-boundary-singular-classes`
(for all algebras whose traces are quasidiagonal) implies the universal
K_0-Hahn--Banach property, so it is not a reduction of it.  Trace-sign
arguments (`stw07-sign-changing-qd-trace-values-kill-class`,
`stw07-quotient-trace-zero-nontorsion-class-is-killed`) settle exactly the
classes that some trace, or some trace-kernel quotient, detects rationally.
The problem lives entirely in trace-invisible classes.
