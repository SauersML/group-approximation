---
rg: 2
id: sofic-subgroup-free-restriction-proof
kind: route
title: Good points of a sofic approximation form free regular D_8-orbits, and (b-1)(a-1) has rank 3 on each
target: sofic-subgroups-carry-rank-models-violating-two-root-identity
requires:
  - finite-subgroup-rank-data-cannot-force-two-root-identity
artifacts:
  - research/artifacts/el3-two-root-identities-2026-09-12.md
---

Complete proof: artifact Section 6.4.

- **The rank model.** Normalized rank distance is at most normalized Hamming distance for
  permutation matrices, so `[P_i]` is multiplicative in the rank ultraproduct.
- **Bad and good points.** Let `B_i` be the points `x` with any of:
  - `phi(d) phi(d') x != phi(dd') x` for some `d, d'` in `D`;
  - `phi(1) x != x`;
  - `phi(d) x = x` for some `d != 1`.
  Then `|B_i| = o(n_i)`. The good points `G_i = { x not in B_i : phi(d) x not in B_i for all d }`
  number at least `n_i - 9 |B_i|`.
- **Free orbits.** For good `x`, `O(x) = { phi(d) x }` is `phi(D)`-invariant, `phi(D)` acts on it
  as the regular action, and two such orbits are equal or disjoint.
- **Correcting the action.** Let `psi` be `phi` on the union `U_i` of these orbits and the identity
  elsewhere. Then `psi` is an honest homomorphism `D -> Sym(n_i)` within `o(1)` of `phi`.
- **The rank.** `F_2^(U_i)` is a free `F_2[D]`-module, on which `(h-1)(g-1)` has rank
  `3 |U_i| / 8` (`finite-subgroup-rank-data-cannot-force-two-root-identity`, value computation).
  Its rank on the complement is `0`. So the normalized rank tends to `3/8`.
