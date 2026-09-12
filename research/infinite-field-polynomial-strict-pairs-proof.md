---
rg: 2
id: infinite-field-polynomial-strict-pairs-proof
kind: route
title: Infinite fields make the identity formal; the prime-field reduction finishes
target: infinite-field-polynomial-strict-pairs-need-kaplansky-failure
requires:
  - formal-polynomial-strict-pairs-need-unstable-linearization
  - stable-finiteness-reduces-to-prime-field
artifacts:
  - research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md
---

Corollary 2 in Section 3 of the artifact.
1. Each coordinate of `sigma o tau - id` is a polynomial in finitely many variables that vanishes on
   every `k`-point. Since `k` is infinite, it is zero, so the identity is formal.
2. By the first prerequisite, a non-bijective `tau` gives a one-sided inverse pair in `M_n(k[G])`,
   so `k[G]` is not stably finite.
3. By the second prerequisite, that is impossible in characteristic 0, and in characteristic `p` it
   is equivalent to `F_p[G]` not being stably finite.
