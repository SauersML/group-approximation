---
rg: 2
id: fpbs-pivotal-kernels-hold-on-known-gap-test-graphs-proof
kind: route
title: Check the strict l2 gap on trees, hyperbolic groups and tree-by-lattice products
target: fpbs-pivotal-kernels-hold-on-known-gap-test-graphs
requires:
  - fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels
  - fpbs-hyperbolic-nonunimodular-critical-l2-gap
artifacts:
  - research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md
---

Written proof, from Section 5.2 of the artifact. Each graph is a nonamenable
Cayley graph with `p_c<p_(2->2)`, so the first prerequisite applies. Each
underlying group contains a free subgroup of rank two, and so each graph is
nonamenable.

* **Trees and hyperbolic groups.** `T_k` is 0-hyperbolic. The Cayley graphs of
  a hyperbolic group are Gromov hyperbolic. Both are covered by the hyperbolic
  case of the second prerequisite.
* **`T_k x Z^m`.** Fix an end `xi` of `T_k` and let
  `H = Aut_xi(T_k) x Z^m` act coordinatewise.
  * `H` is transitive, because `Aut_xi(T_k)` is vertex-transitive on `T_k`.
  * `H` is closed in `Aut(G)`. Along a pointwise convergent sequence
    `(g_i,t_i)`, `t_i` is eventually constant and `g_i` converges in the closed
    subgroup `Aut_xi(T_k)`.
  * Let `y` be the neighbour of `x` toward `xi`. The stabilizer of `(x,z)` in
    `H` fixes the ray from `x` to `xi`, so the orbit of `(y,z)` under it has
    size `1`.
  * The stabilizer of `(y,z)` moves `(x,z)` through the `k-1` neighbours of
    `y` away from `xi`.

  So `H` is nonunimodular, and the nonunimodular case of the second
  prerequisite applies.
* **Neither hyperbolic nor a cactus.** For `m>=1` the product contains an
  isometric square grid: a geodesic line of `T_k` times the `e_1` axis. So it
  is not hyperbolic. Each `e_1` edge lies on at least `k` distinct 4-cycles,
  so it is not a cactus.
