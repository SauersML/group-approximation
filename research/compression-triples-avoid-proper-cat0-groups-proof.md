---
rg: 2
id: compression-triples-avoid-proper-cat0-groups-proof
kind: route
title: Nest commuting copies of the factor, extract free abelian subgroups of every rank, and bound the rank by the Flat Torus Theorem
target: compression-triples-avoid-proper-cat0-groups
requires: [kazhdan-compression-instances-have-infinite-vcd]
---

Let `X` be the complex and `d = dim X`. Suppose `J` is infinite.

1. **Nesting.** By `kazhdan-compression-instances-have-infinite-vcd` (N1), for every `n` the
   conjugates `J_k = t^k J t^(-k)`, `1 <= k <= n`, lie in `Gamma` and generate an internal direct
   product `J_1 x ... x J_n <= G`.
2. **An element of infinite order.** `J` is finitely generated and infinite, so by hypothesis it
   is not a torsion group. Pick `j in J` of infinite order and let `j_k = t^k j t^(-k) in J_k`.
3. **Free abelian subgroups.** Take `n = d + 1`. The `j_k` commute, and the product
   `J_1 x ... x J_n` is direct, so `A = <j_1, ..., j_n>` is free abelian of rank `n`.
4. **Semisimplicity.** A cellular isometry of an `M_kappa`-polyhedral complex with finitely many
   shapes is semisimple (Bridson 1999). So `A` acts by semisimple isometries, properly since `G`
   does.
5. **Flat Torus Theorem** (Bridson--Haefliger II.7.1). `Min(A)` is nonempty and splits as
   `Y x E^n`. So `X` contains an isometrically embedded `E^n`.
6. **Dimension.** A polyhedral complex of dimension `d` contains no topologically embedded
   `n`-ball with `n > d`: such a ball would meet the interior of some closed cell of dimension
   `m <= d` in an open subset of `R^n`, which invariance of domain forbids. So `n <= d`, a
   contradiction.

Therefore `J` is finite.
