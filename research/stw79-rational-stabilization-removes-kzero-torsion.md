---
rg: 2
id: stw79-rational-stabilization-removes-kzero-torsion
kind: claim
title: Rational stabilization removes the quotient K-zero torsion restriction in the AF-ideal index dichotomy
artifacts:
  - research/artifacts/stw79-rational-index-criterion-2026-09-05.md
---

Let `B` be a separable infinite-dimensional simple unital AF algebra with
totally ordered `K_0(B)`, and `D` a separable simple unital non-elementary
nuclear UCT algebra of finite decomposition rank. No restriction on
either K-group of `D` is imposed. Given a unital essential extension

```text
0 -> K tensor B -> E -> D -> 0,
```

let `delta:K_1(D)->K_0(B)` be its index and let `Q` be the universal UHF
algebra. Write `d_Q=dr(D tensor Q)`. Then

```text
dr(E tensor Q) = d_Q       if delta=0,
dr(E tensor Q) = infinity  if delta!=0.
```

In this class the following are equivalent:

```text
delta=0;
E is stably finite;
E is quasidiagonal;
dr(E tensor Q)<infinity.
```

This does not assert that `dr(E)` is finite in the zero-index case.
The quasidiagonality/index equivalence is existing Brown–Dadarlat prior
art; the displayed rational decomposition-rank formula follows from
`stw79-total-order-af-index-dr-dichotomy`. It isolates a rational descent
issue for the remaining LXXIX cases with quotient K-zero torsion.
