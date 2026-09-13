---
rg: 2
id: non-lef-kazhdan-el-group-from-fp-rank-modelled-simple-algebra
kind: route
title: A finitely presented infinite simple rank-modelled algebra is never exactly matricial, so the LEF converse leaves some Kazhdan elementary group over it non-LEF
target: rank-modelled-simple-algebra-with-non-lef-kazhdan-el-group
requires:
  - fp-simple-algebra-over-finite-field-with-rank-model
  - lef-el-groups-force-exactly-matricial-simple-ring
  - exactly-matricial-rings-are-lef-rings
  - lef-simple-rings-are-not-finitely-presented
  - elementary-groups-over-fg-rings-have-property-t
artifacts:
  - research/artifacts/un-blueprint-2026-09-13-part1.md
---

**Derivation.**
1. `fp-simple-algebra-over-finite-field-with-rank-model` gives a finitely presented, infinite-dimensional,
   simple unital algebra `R` over a finite field `k`, with a unital rank model over `k`.
2. `k = F_q` is finitely presented as a ring, so a finitely presented `k`-algebra is a finitely presented
   ring. In particular `R` is finitely generated.
3. `R` is infinite, finitely presented and simple, so it is not a LEF ring
   (`lef-simple-rings-are-not-finitely-presented`).
4. So `R` is not exactly matricial, since exactly matricial rings are LEF rings
   (`exactly-matricial-rings-are-lef-rings`).
5. By the contrapositive of `lef-el-groups-force-exactly-matricial-simple-ring`, not every `EL_N(R)` with
   `N >= 3` is LEF. Fix `N >= 3` with `EL_N(R)` not LEF.
6. `R` is finitely generated, so `EL_N(R)` is Kazhdan (`elementary-groups-over-fg-rings-have-property-t`).

This establishes the target with the same `R` and `N`.
