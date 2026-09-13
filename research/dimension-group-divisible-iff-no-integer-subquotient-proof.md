---
rg: 2
id: dimension-group-divisible-iff-no-integer-subquotient-proof
kind: route
title: Realize the dimension group as K_0 of an AF algebra and match integer layers with elementary subquotients
target: dimension-group-divisible-iff-no-integer-subquotient
requires: [af-k0-order-divisible-iff-no-elementary-subquotient]
---

By Effros--Handelman--Shen, `G` is order-isomorphic to `K_0(C)` for an AF
algebra `C`.  (ND) is a property of the ordered group, so by
`af-k0-order-divisible-iff-no-elementary-subquotient` it holds iff `C` has no
elementary subquotient.  It remains to show that `C` has an elementary
subquotient iff `G` has an order-subquotient isomorphic to `(Z, N)`.

These are standard facts for AF algebras (Elliott).

* Closed ideals of `C` correspond bijectively to order ideals of `K_0(C)`
  via `I |-> K_0(I)`.
* For ideals `I subset J`, the six-term sequence (with `K_1 = 0` for AF
  algebras) gives `K_0(J/I) = K_0(J)/K_0(I)`.
* Projections lift from `J/I` to `J`, so the positive cone of `K_0(J/I)` is
  the image of `K_0(J)^+`.

So order-subquotients `J/I` of `G` are exactly the ordered groups `K_0(J/I)`.

* If `J/I` is elementary, `K_0(J/I)` is `(Z, N)`.
* Conversely, if `K_0(J/I)` is `(Z, N)`, then `J/I` has no nontrivial ideals,
  since `(Z, N)` has no nontrivial order ideals.  A simple AF algebra with
  `K_0 = (Z, N)` has a projection of class `1`, which is minimal.  So `J/I` is
  a simple algebra with a minimal projection, hence elementary.
