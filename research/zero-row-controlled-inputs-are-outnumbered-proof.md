---
rg: 2
id: zero-row-controlled-inputs-are-outnumbered-proof
kind: route
title: Coarse inverses and one private real coordinate kill each input class over small shared boxes, covering dimension bounds the killed inputs by the shared rows, and a random shared set gives the constant
target: zero-row-controlled-inputs-are-outnumbered
requires: []
artifacts:
  - research/artifacts/zero-row-slice-count-2026-09-20.md
---

Full proof in `research/artifacts/zero-row-slice-count-2026-09-20.md`, Sections 1 to 4.

1. **Lemma N.** Partition-of-unity gluing gives `psi_i` on an open `U_i ⊇ g_(C_i)(T^n)` with
   `psi_i o g_(C_i) ≃ pi_i`.
2. **Lemma S.** Lift the zero rows to `Phi: T^n -> R^(Z_0)`. If `|C_i \ Z| <= 1`, then `pi_i` vanishes on
   `Phi_Z^-1(O)` for every small open `O`.
   - The slices of `U~` over the shared coordinates are open subsets of `R`.
   - Together with the tube lemma, this puts the image in a disjoint union of convex boxes inside `U~`.
3. **Lemma LS.** Colour the open stars of a fine barycentric subdivision of `R^Z` by dimension. This gives
   `|Z| + 1` families, each made of disjoint small sets.
   - Relative cup products show that any `|Z| + 1` of the classes have product `0`.
   - So `|X| <= |Z|`.
4. **Count.** For every `T ⊆ P_0`, `|{i : |C_i ∩ T| <= 1}| <= |P_0| - |T|`. Take `T` random with density
   `p`, then optimise at `p = 1/(K-1)^2`.
5. **Corollary.** Pass to real coordinates, with `K` replaced by `dK`.
