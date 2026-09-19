---
rg: 2
id: stw99-lxvi-car-corner-forces-unbounded-stability-indices
kind: claim
title: A finite CAR corner in a simple mixed algebra forces unbounded matrix-stability indices
distinct_from:
  stw99-lxvi-k0-dyadic-divisibility-obstruction: that detects failure of dyadic roots in K0; this gives a projection-theoretic obstruction even when all K0 divisibility tests vanish.
---

Let `B` be simple and contain an infinite projection.  Suppose `p in B` is a
nonzero finite projection and `pBp` contains CAR unitally.  Then there are
nested nonzero finite projections

```text
p=p_0 >= p_1 >= p_2 >= ...
```

such that every corner `p_n B p_n` is not stably finite, but the units of all
its matrix amplifications of sizes at most `2^n` are finite.

Equivalently, if `mu(q)` is the least matrix size for which the unit of
`M_(mu(q))(qBq)` is infinite, then

```text
mu(p_n)>2^n.
```

Consequently, if a simple mixed finite-infinite algebra has a uniform bound
on `mu(q)` over its nonzero finite projections, none of its finite corners can
contain CAR unitally.
