---
rg: 2
id: weak-sofic-stable-finiteness-from-surjunctivity
kind: route
title: Surjunctive groups have stably finite group algebras over finite fields, so weak-sofic surjunctivity gives the linear shadow
target: weakly-sofic-group-algebras-are-stably-finite
requires:
  - weakly-sofic-groups-are-surjunctive
  - stable-finiteness-failure-refutes-surjunctivity
artifacts:
  - research/artifacts/metric-ultraproduct-bounded-width-closure-2026-09-12.md
---

Take a weakly sofic `G` and suppose `M_n(F_q[G])` contains `A, B` with `BA = I_n` and `AB != I_n`. By
`stable-finiteness-failure-refutes-surjunctivity`, `G` then carries an injective non-surjective automaton over the
alphabet `F_q^n`, which contradicts `weakly-sofic-groups-are-surjunctive`.
