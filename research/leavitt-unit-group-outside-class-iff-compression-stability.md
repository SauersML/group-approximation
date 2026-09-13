---
rg: 2
id: leavitt-unit-group-outside-class-iff-compression-stability
kind: claim
title: In every metric class, the binary Leavitt unit group lies outside the class exactly when Kazhdan centralizers normalize uniformly at the nine-leaf pair
distinct_from:
  kazhdan-commutant-compression-stability-is-finitary: that is the class-independent equivalence between normalization and the uniform inequality at any rigid pair; this shows that at the nine-leaf Leavitt pair both are further equivalent to the Leavitt unit group being outside the class, so the criterion loses nothing there.
  leavitt-pair-vertex-rounding-is-nonhyperlinearity: that equates vertex rounding (H1) at this pair with nonhyperlinearity of the unit group; this equates normalization and the uniform inequality with non-membership, in all four metric classes at once.
  binary-leavitt-unit-group-hyperlinear: that is the open claim that the unit group is hyperlinear; this proves that claim is equivalent to failure of one uniform centralizer inequality at the nine-leaf pair, and records the parallel equivalences in the other three classes.
artifacts:
  - research/artifacts/unified-compression-rigidity-part2-2026-09-12.md
---

**ESTABLISHED.** Let `R = L_(F_2)(1,2)` and take the nine-leaf configuration of
`openai-nine-leaf-leavitt-configuration`: `Gamma = EL_alpha(R) <= G_L = EL_D(R) = R^x`, with
compressors `u, v` and `G_L = <Gamma, u, v>`. Let `F` be a finite symmetric generating set of
`Gamma`. For `C` sofic, hyperlinear, `k`-linear sofic (any field `k`) or weak MF, the following
are equivalent.

1. `R^x` is not in `C`.
2. `NORM_C`: for every metric ultraproduct `U` of the model groups of `C` and every homomorphism
   `sigma : R^x -> U`, the group `sigma(R^x)` normalizes `C_U(sigma(Gamma))`.
3. `UCS_C(F, {u, v})` of `kazhdan-commutant-compression-stability-is-finitary`: uniformly in the
   dimension, approximate models that almost commute with `Gamma` stay almost commuting after
   conjugation by `u` and `v`.

## Reading

- **The criterion is exact at this pair.** For the Kun--Thom wreath, normalization is only
  sufficient for non-membership. At the Leavitt pair nothing is lost: `R^x` is simple, so every
  wall comes from a faithful model.
- **Four famous questions about one group, as one inequality in four metrics.**
  - *Hamming.* (3) holds (`sofic-groups-kill-rigid-compression-defects`), which recovers that `R^x`
    is not sofic.
  - *Hilbert--Schmidt.* (3) is equivalent to `R^x` not hyperlinear. Its failure is
    `binary-leavitt-unit-group-hyperlinear`, which makes `R^x` a hyperlinear nonsofic group.
  - *Rank over `F_2`.* (3) is equivalent to the negative answer to
    `binary-leavitt-unit-group-is-f2-linear-sofic`, the gate of the Gottschalk campaign.
  - *Operator norm.* (3) is equivalent to `R^x` not weak MF, and it holds: every homomorphism
    from `R^x` to an MF group is trivial (`binary-leavitt-all-ranks-full-mf-radical`). The same
    inequality fails at the Kun--Thom Theorem E pair
    (`kazhdan-commutant-compression-stability-is-finitary`, weak MF row). So in the operator norm
    the inequality separates the two configurations.
- **At this pair, all known Hilbert--Schmidt handles coincide.** With
  `leavitt-pair-vertex-rounding-is-nonhyperlinearity`: vertex rounding (H1), the uniform inequality,
  normalization for every model, and nonhyperlinearity of `R^x` are the same statement.

Derivation: `leavitt-unit-group-outside-class-iff-compression-stability-proof`.
