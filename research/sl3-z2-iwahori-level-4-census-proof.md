---
rg: 2
id: sl3-z2-iwahori-level-4-census-proof
kind: route
title: Reduce to subspaces of sl_3(F_2) avoiding the 28 rank-2 idempotents, then enumerate
target: sl3-z2-iwahori-index-8-torsion-free-misses-level-4
requires: []
---

Let `U` be the unitriangular group of `SL_3(F_2)`, `V = K_1/K_2`, and put
`K = W cap K_1`. Let `W-bar` be the image of `W` in `U`.

**Reduction.**
- **Indices.** `[I:W] = [U : W-bar][K_1 : K] = 8`, so `|W-bar| = 2^c` and
  `[K_1:K] = 2^c` for some `c` in `{0,1,2,3}`.
- **Orders.** `(I+2y)(I+2z) = I + 2(y+z) mod 4`, so `V` is elementary abelian of
  order `2^8`. `det(I+2y) = 1 + 2 tr(y) mod 4` gives
  `V = {y in M_3(F_2) : tr y = 0}`.
- **Subspace.** If `K_2 <= W` then `S = K/K_2` is a subspace of codimension `c`.
  It is normalized by `W-bar`, since conjugation by `K_1` is trivial on `V`.
- **Avoidance.** For a rank-2 idempotent `ebar` over `F_2`, lift it to an
  idempotent `e` over `Z_2`. Then `I - 2e` is an involution in the coset
  `I + 2 ebar + K_2`. So a torsion-free `W` needs `S` to contain none of the 28
  rank-2 idempotents.
- **Small `c`.** The case `c = 0` is `S = V`. For `c = 1`, a hyperplane avoiding
  the 28 would contain an avoiding codimension-2 subspace.

**Census** (`experiments/strong-atiyah-sl3z/iwahori_level4_census.py`, output
in `iwahori_level4_census.out`). The script represents functionals
`y -> tr(cy)` with `c` modulo `I`. It enumerates all 2- and 3-element sets of
functionals whose common kernel misses the 28 idempotents, and tests
normalization under each order-4 and order-8 subgroup of `SL_3(F_2)`:
- no codimension-2 subspace avoids the 28;
- 1500 codimension-3 subspaces avoid them, and none is normalized by any of the
  21 subgroups of order 8, all of which are Sylow and conjugate to `U`.

So no case survives.
