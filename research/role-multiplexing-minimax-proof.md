---
rg: 2
id: role-multiplexing-minimax-proof
kind: route
title: Compute the exact trace and optimize the finite role weights
target: role-multiplexing-is-minimax-max-selection
requires: []
---

Pairwise orthogonality of the role projections gives

```text
(sum_i R_i tensor P_i)^2=sum_i R_i tensor P_i,
```

without any commutation assumption among the payload projections.  Product
trace gives `(ORM3)`.

Let `r_min=min_i r_i`.  Positivity and `(ORM4)` imply

```text
sum_i r_i tau(P_i)>=r_min sum_i tau(P_i)>=r_min V.
```

This constant is sharp: concentrate the prescribed trace in a type whose
role weight is `r_min` and take every other payload projection to be zero.
Since `sum_i r_i<=1`, one has `r_min<=1/M`; equal role weights attain
`1/M`.  This proves `(ORM5)--(ORM7)`.

For the fixed-group realization, restrict an extraspecial `2`-group to its
unique negative-central-character sector.  Finite Stone--von Neumann gives
`C^(2^k) tensor H`, its diagonal character atoms have weight `2^(-k)`, and
the commuting BCS tuple lies in the multiplicity commutant.  The preceding
calculation applies verbatim.  Fixed finite-group HS exactification and
averaging into the packet commutant add only a dimension-independent
`O(sqrt(E))` perturbation.
