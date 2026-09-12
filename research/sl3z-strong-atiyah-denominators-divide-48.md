---
rg: 2
id: sl3z-strong-atiyah-denominators-divide-48
kind: claim
title: Von Neumann ranks of matrices over C[SL_3(Z)] lie in (1/48)Z
distinct_from:
  congruence-kazhdan-groups-satisfy-strong-atiyah: that is integrality of ranks for torsion-free congruence subgroups; this transfers it to SL_3(Z) itself, which has torsion, with denominator 48.
  raag-out-and-mapping-class-virtually-strong-atiyah: that gives the Weak Atiyah Conjecture (some discrete subgroup of Q) for Out and mapping class groups; this pins the exact denominator bound for SL_3(Z).
artifacts:
  - research/artifacts/strong-atiyah-kazhdan-groups-2026-09-12.md
---

**ESTABLISHED** by [[sl3z-atiyah-denominators-48-proof]].

For every finite matrix `A` over `C[SL_3(Z)]`,

    48 * rk_{N(SL_3(Z))}(A) in Z.

Strong Atiyah for `SL_3(Z)` predicts the denominator `lcm = 24`, since the
finite subgroups have orders dividing 24 and `S_4` occurs. So this bound is off
by exactly a factor 2. `sl3z-satisfies-strong-atiyah` records the remaining
question.
