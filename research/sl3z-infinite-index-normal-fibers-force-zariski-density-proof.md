---
rg: 2
id: sl3z-infinite-index-normal-fibers-force-zariski-density-proof
kind: route
title: Rule out each non-dense case, then apply Margulis's normal subgroup theorem
target: sl3z-infinite-index-normal-fibers-force-zariski-density
requires:
  - sl3z-non-dense-subgroups-classified
artifacts:
  - research/artifacts/zp-sl3z-coherence-non-dense-2026-09-13-part2.md
---

Fact (Φ): a finitely generated non-elementary virtually free group, or a
virtually closed-surface group of genus at least 2, has no infinite finitely
generated normal subgroup of infinite index. Its first L²-Betti number is
positive (Gaboriau 2002); classically, use Schreier for free groups and
Griffiths for surface groups.

Suppose `K` is not dense and use `sl3z-non-dense-subgroups-classified`.

- **(V)** `N` would be virtually solvable.
- **(F)** `K` is a non-elementary finitely generated Fuchsian group up to
  index 2, so (Φ) applies.
- **(P)** Let `π: P -> GL_2(Z)` with kernel `U ≅ Z^2`. Put `V = K ∩ U` and
  `W = N ∩ U`.
  1. `π(N)` is not virtually solvable, so (Φ) gives `[π(K) : π(N)] < ∞`.
  2. Hence `[V : W] = ∞`.
  3. Commutators `[n, v]` lie in `W`, so `π(N)` acts trivially on
     `V_Q/W_Q` and preserves `W_Q`. The action of `GL_2(Z)` on `U` is
     faithful.
  4. So `π(N)` fixes a nonzero vector (if `W_Q = 0`) or lies in a Borel
     subgroup (if `dim W_Q = 1`). Either way it is solvable, a contradiction.

So `K` is dense. Then:

- The identity component of the Zariski closure of `N` is a connected normal
  subgroup of `SL_3`, and it is nontrivial because `N` is not virtually
  solvable. So `N` is dense.
- A finite-index `K` would be a lattice in `SL_3(R)`. Margulis's normal
  subgroup theorem would then make `N` finite or of finite index.

This is Theorem 6.1 of the artifact.
