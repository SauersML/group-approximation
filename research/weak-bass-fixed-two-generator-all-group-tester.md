---
rg: 2
id: weak-bass-fixed-two-generator-all-group-tester
kind: claim
title: One two-generator finitely presented group tests the integral weak Bass conjecture for every group
distinct_from:
  weak-bass-fixed-two-generator-torsion-free-tester: that uses a torsion-free host and quantifies only over torsion-free groups; this is the unrestricted all-group tester.
  classical-bass-fixed-two-generator-testers: classical Bass controls every nonidentity conjugacy-class component and needs Frattini embeddings; weak Bass compares only augmentation with the identity coefficient and is inherited by ordinary subgroup embeddings.
  universal-all-group-subgroup-colimit-class-tester: that is property-independent; this verifies the weak Bass trace identity has the required permanence.
---

For a group `G`, let

~~~text
epsilon_G,kappa_G:K_0(Z[G]) -> Z
~~~

be the augmentation and Kaplansky traces. The integral weak Bass conjecture
for `G` is `epsilon_G=kappa_G`.

There exists one fixed two-generator finitely presented group `U` such that

~~~text
epsilon_U=kappa_U
  <=>
epsilon_G=kappa_G for every group G.
~~~

The host is the torsionful all-group host in
[[universal-all-group-subgroup-colimit-class-tester]]. This is an exact
reduction, not a proof of the weak Bass conjecture.

**ESTABLISHED 2026-08-31** by
[[weak-bass-all-group-tester-proof]].
