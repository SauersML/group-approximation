---
rg: 2
id: torsion-free-non-mf-from-infinite-order-mark
kind: route
title: Mark an infinite-order central element and detect it on a commutant corner
target: torsion-free-finitely-presented-non-mf
requires: [infinite-order-central-mark-group, commutant-projection-extraction]
---

## Why sufficient

Let `H` be the torsion-free finitely presented group of
`infinite-order-central-mark-group` and let `z != 1` be its central mark,
lying in the normal closure of the compression defect.

Let `Theta` be any corona representation of `H`.  By clause 1 of
`corona-corner-detection-criterion`, applied in every corner cut by a
nonzero projection of the relative commutant `Theta(H)' cap Q`,

    ‖q Theta(z) q - q‖_2 = 0   for every such q.

That is exactly the hypothesis of `commutant-projection-extraction`, whose
conclusion is `Theta(z) = 1`.  Since `z != 1` in `H`, no corona
representation of `H` is injective, so `H` is not MF; and `H` is
torsion-free and finitely presented.

The two prerequisites are independent: the first is group theory (build the
mark), the second is operator algebra (detect it without a spectral gap).
Neither uses the order of `z`, which is the whole point — the order-two
hypothesis of `central-sign-corona-obstruction` is consumed only in
supplying the projection that the second prerequisite must supply by other
means.
