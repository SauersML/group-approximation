---
rg: 2
id: coprime-root-reynolds-overlap-proof
kind: route
title: Expand both finite Fourier averages and use coprime subgroup intersection
target: coprime-root-reynolds-prefix-overlap
requires: []
---

Expand `e_chi P_(z,1)` in the canonical group basis.  A summand has nonzero
trace precisely when `h z^k=1`.  This puts `h` in
`H intersect <z>`, which is trivial because `H` has two-power order and
`z` has odd prime order.  Only the identity summand remains, giving
`1/(|H|p)`.  Subtract from `tau(e_chi)=1/|H|`.  In canonical microstates the
same finite expansion converges term by term; fixed finite-group
exactification and telescoping give the dimension-free robust form.
