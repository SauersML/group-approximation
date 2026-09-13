---
rg: 2
id: no-heisenberg-from-finite-centralizer-rank
kind: route
title: Finite centralizer rank of every infinite-order unit excludes H_3(Z) from the binary Leavitt unit group
target: leavitt-unit-group-has-no-integer-heisenberg-subgroup
requires: [leavitt-unit-centralizers-have-finite-rank, leavitt-heisenberg-centers-have-infinite-centralizer-rank]
---

1. A subgroup `H_3(Z) <= Q = L_(F_2)(1,2)^x` gives `a, b` with `c = [a,b]` central in `<a,b>` and of infinite
   order.
2. By `leavitt-heisenberg-centers-have-infinite-centralizer-rank` (i), `rho(c) = ∞`.
3. By `leavitt-unit-centralizers-have-finite-rank`, `rho(c) < ∞`. This is a contradiction, so `Q` has no
   subgroup `H_3(Z)`. ∎

With part (iii) of the first premise, the same two premises exclude every `BS(1,k)` with `|k| >= 2`.
