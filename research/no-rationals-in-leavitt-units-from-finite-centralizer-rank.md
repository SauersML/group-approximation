---
rg: 2
id: no-rationals-in-leavitt-units-from-finite-centralizer-rank
kind: route
title: Finite centralizer rank of every infinite-order Leavitt unit excludes (Q,+) from the binary Leavitt unit group
target: rationals-do-not-embed-in-binary-leavitt-unit-group
requires: [leavitt-unit-centralizers-have-finite-rank, unit-roots-divide-centralizer-rank]
---

1. Suppose `(Q,+) <= U = L_(F_2)(1,2)^x`, and let `x` be the image of `1`. It has infinite order, and for every
   `k >= 1` it is the `k`-th power of the image of `1/k`.
2. By `unit-roots-divide-centralizer-rank`, parts 2 and 3, `rho(x) = ∞`.
3. By `leavitt-unit-centralizers-have-finite-rank`, `rho(x) < ∞`. This is a contradiction. ∎
