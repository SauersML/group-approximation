---
rg: 2
id: sl3z-is-coherent-via-dense-and-non-dense-cases
kind: route
title: Split finitely generated subgroups of SL_3(Z) by Zariski density
target: sl3z-is-coherent
requires:
  - non-zariski-dense-subgroups-of-sl3z-are-coherent
  - finitely-generated-dense-subgroups-of-sl3z-are-fp
---

A finitely generated subgroup `K <= SL_3(Z)` either has proper Zariski
closure or is Zariski-dense.

- In the first case `K` is finitely presented by
  `non-zariski-dense-subgroups-of-sl3z-are-coherent`.
- In the second case it is finitely presented by
  `finitely-generated-dense-subgroups-of-sl3z-are-fp`.

This is a genuine case split, not a restatement. The established claim
removes every non-dense subgroup, and the open claim concerns only Zariski-dense
subgroups, which are automatically finitely presented when of finite index.
The prerequisite can fail on its own (a dense thin counterexample) without
mentioning the non-dense subgroups at all.
