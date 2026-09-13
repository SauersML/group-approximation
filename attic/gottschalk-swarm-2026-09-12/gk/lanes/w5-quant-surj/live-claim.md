---
rg: 2
id: quantitative-surjunctivity-constants-lift-from-quotients
kind: claim
title: A subshift missing a configuration invariant under a normal subgroup inherits the quantitative surjunctivity constant of its quotient restriction
distinct_from:
  surjunctive-groups-are-quantitatively-surjunctive: that asks for a constant for every proper subshift over every surjunctive group; this supplies one for every subshift missing a configuration invariant under a normal subgroup with quantitatively surjunctive quotient, leaving only the subshifts that contain all such configurations.
  surjunctive-groups-are-uniformly-quantitatively-surjunctive: that asks for constants uniform over tracks missing different patterns; this is the restriction step for one fixed subshift and gives no uniformity.
artifacts:
  - research/artifacts/quantitative-surjunctivity-residue-2026-09-12.md
---

**ESTABLISHED** by `quotient-restriction-deficit-proof`.

**Theorem.** Let `N` be normal in `G`, and `Y <= B^G` a subshift not containing `Fix_N`. Let `Y_N <= B^(G/N)` be the
proper subshift corresponding to `Y cap Fix_N`. Every quantitative surjunctivity constant of `Y_N` over `G/N` is
one of `Y` over `G`.

**Corollaries** (Section 2 of the artifact).
- **Constant configurations, every group.** If `Y` has `c_Y < |B|` constant configurations, `log(|B| / c_Y)` is a
  constant.
- **Periodic points.** For `H` of finite index `m`, `log(|B|^m / |Y cap Fix_H|) / m` is a constant when positive.
- **Residually finite groups.** They are quantitatively surjunctive with constant `-log(1 - |B|^(-|W|)) / |W|^2`
  for a pattern on `W` missing from `Y`. The proof uses periodic points and no sofic models.
- **Residue.** Using the sofic count recorded in `surjunctive-groups-are-quantitatively-surjunctive`, `G` is
  quantitatively surjunctive iff every proper subshift containing `Fix_N` for every normal `N` with `G/N` sofic has
  a constant.
  - For groups with no nontrivial sofic quotient, finitely generated simple nonsofic groups included, these are
    the proper subshifts containing all constant configurations.

Proof: Section 2 of the artifact.
