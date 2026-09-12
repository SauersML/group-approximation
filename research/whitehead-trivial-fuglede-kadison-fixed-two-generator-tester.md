---
rg: 2
id: whitehead-trivial-fuglede-kadison-fixed-two-generator-tester
kind: claim
title: One two-generator finitely presented group tests triviality of the Fuglede--Kadison determinant on every Whitehead group
distinct_from:
  luck-determinant-fixed-two-generator-tester: Lueck's determinant conjecture is the stronger lower bound for every integral group-ring matrix and implies this conjecture; this asks only that the determinant homomorphism on Whitehead classes be trivial.
  classical-bass-fixed-two-generator-testers: that concerns the Hattori--Stallings trace on `K_0(Z[G])`; this concerns the Fuglede--Kadison determinant on `Wh(G)`.
  whitehead-universal-finitely-presented-container: that supplies the fixed host and injects Whitehead groups; this tests a numerical homomorphism defined on them.
---

For a group `G`, the Fuglede--Kadison determinant induces a homomorphism

~~~text
Phi_G:Wh(G) -> R_(>0).
~~~

Lueck's Whitehead-determinant conjecture says that `Phi_G` is trivial for
every group.

There exists one fixed two-generator finitely presented group `U` such that

~~~text
Phi_U is trivial
  <=>
Phi_G is trivial for every group G.
~~~

The host is the all-group group in
[[universal-all-group-subgroup-colimit-class-tester]], with every finite
torsion order. This is an exact reduction only. Lueck's stronger determinant
conjecture would imply the positive side, but is not assumed here.

**ESTABLISHED 2026-08-31** by
[[whitehead-trivial-determinant-fixed-tester-proof]].
