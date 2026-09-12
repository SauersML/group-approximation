---
rg: 2
id: atlas-mcl-contains-no-a8
kind: claim
title: The McLaughlin group contains no subgroup A8
distinct_from:
  atlas-a8-index-12481-to-44550-reaches-mcl: that identifies McL only as an order-divisible endpoint; this proves the divisibility is not realized by a subgroup.
  atlas-a8-index-91-to-496-reaches-standard-l5: that already removes U4(3) and M22 as A8 carriers; this applies those exclusions inside McL and removes the remaining maximal types.
---

The simple McLaughlin group `McL` contains no subgroup isomorphic to `A8`.

The official maximal-subgroup list, filtered by divisibility by `20160`,
leaves precisely

```text
U4(3),
M22                         (two classes),
L3(4).2_2,
2.A8,
2^4:A7                     (two classes).           (MCLA8-1)
```

None contains `A8`:

1. The maximal-subgroup tables of `U4(3)` and `M22` leave only an
   equal-order `L3(4)` carrier.  It is not isomorphic to `A8`.
2. If `A~=A8 < L3(4).2_2`, simplicity forces `A` into the normal index-two
   socle `L3(4)`; equality of orders again gives the impossible
   `A8 ~= L3(4)`.
3. If `A~=A8 < 2.A8`, then `A` has trivial intersection with the central
   subgroup of order two and maps isomorphically onto the quotient `A8`.
   That would split the nonsplit double cover `2.A8`.
4. If `A~=A8 < 2^4:A7`, then `A intersect 2^4` is normal in simple `A`, so
   is trivial.  Projection would inject `A8` into `A7`, contradicting
   orders.

Thus no maximal subgroup of `McL` contains `A8`, and neither does `McL`.

Sources: the GAP Character Table Library maximal-subgroup tables for
[`McL`](https://www.math.rwth-aachen.de/homes/Thomas.Breuer/ctbllib/ctbltoc/data/McL.html),
[`U4(3)`](https://www.math.rwth-aachen.de/homes/Thomas.Breuer/ctbllib/ctbltoc/data/U4%283%29.html),
and [`M22`](https://www.math.rwth-aachen.de/homes/Thomas.Breuer/ctbllib/ctbltoc/data/M22.html).

