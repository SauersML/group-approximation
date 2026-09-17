---
rg: 2
id: left-orderable-non-sofic-via-compiler-rope
kind: route
title: If some compiler rope R_e is not sofic, it is a finitely presented locally indicable nonsofic group
target: left-orderable-non-sofic-group
requires: [compiler-positive-rope-is-not-sofic, compiler-rope-is-locally-indicable]
---

The group `R_e` is locally indicable ([[compiler-rope-is-locally-indicable]]), so it is left-orderable by
Burns--Hale.  If it is not sofic ([[compiler-positive-rope-is-not-sofic]]), it is a left-orderable nonsofic group.
It is also finitely presented, locally indicable and unique-product.  ∎

**Why this route is not behind Navas's Question 3.**
- `R_e` is locally indicable, so it has no nontrivial Kazhdan subgroup, and no rigid-defect mechanism is involved.
- Unlike the Thompson and Lodha--Moore routes, the input is not an isolated conjecture about one classical group.
  By `sofic-fp-pi2-complete-or-locally-indicable-nonsofic-group`, its failure has a proved consequence:
  `SOFIC_fp` is `Pi^0_2`-complete.
- So the input is attacked from two independent sides:
  - a nonsoficity certificate for `R_e`;
  - any proof that `SOFIC_fp` is *not* `Pi^0_2`-hard.
