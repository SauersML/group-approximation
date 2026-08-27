---
rg: 2
id: atlas-g24-contains-no-a8
kind: claim
title: The simple group G2(4) contains no subgroup A8
distinct_from:
  atlas-a8-index-12145-to-12480-reaches-g24: that identifies G2(4) only as an order-divisible endpoint; this proves Lagrange divisibility is not realized by a subgroup.
  atlas-a8-index-33-to-89-is-orthogonal-sp6: that classifies actual A8 subgroups in a different low-rank classical group.
  atlas-mcl-contains-no-a8: that removes the later sporadic endpoint McL through a different maximal-carrier list.
---

The simple group `G2(4)` has no subgroup isomorphic to `A8`.

Its official maximal-subgroup list has only two rows whose orders are
divisible by `20160`:

```text
J2,                    order 604800,
3.L3(4).2_3,           order 120960.                 (G24A8-1)
```

The first cannot contain `A8`: every maximal subgroup of `J2` has order at
most `6048`, strictly below `20160`.

For the second, let `K=3.L3(4).2_3` and suppose `A~=A8<K`.  Intersecting with
the normal index-two subgroup `3.L3(4)` gives a normal subgroup of simple
`A`; the induced map to `C2` cannot be injective, so `A<=3.L3(4)`.  Its
intersection with the central subgroup of order three is trivial.  Therefore
its image in `L3(4)` has order `20160`, forcing an isomorphism
`A8~=L3(4)`, contrary to the two distinct simple groups of that order.

Sources: the GAP Character Table Library maximal-subgroup tables for
[`G2(4)`](https://www.math.rwth-aachen.de/homes/Thomas.Breuer/ctbllib/ctbltoc/data/G2%284%29.html)
and [`J2`](https://www.math.rwth-aachen.de/homes/Thomas.Breuer/ctbllib/ctbltoc/data/J2.html).
