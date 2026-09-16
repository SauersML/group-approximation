---
rg: 2
id: sl3z-incoherent-via-bieri-normal-subgroup
kind: route
title: A non-free finitely generated normal subgroup of infinite index in a two-dimensional subgroup is not finitely presented, by Bieri
target: sl3z-is-incoherent
requires:
  - sl3z-contains-cd2-group-with-fg-nonfree-normal-subgroup
artifacts:
  - research/artifacts/sl3z-normal-f2-obstruction-2026-09-16.md
---

Let `G <= SL_3(Z)` be finitely generated with `cd G <= 2`, and let `N ◁ G` be
finitely generated, not free, and of infinite index. Then `cd G = 2`, since
groups of cohomological dimension at most 1 are free (Stallings–Swan) and so
are their subgroups.

**Import.** Bieri's theorem, as quoted in the proof of Proposition 5.2 of
D. D. Long and A. W. Reid, *Small subgroups of SL(3,Z)* (preprint dated August
18, 2010, read 2026-09-16): "in a group of cohomological dimension 2, any
finitely presented normal subgroup is free or it is of finite index". The
original is R. Bieri, *Normal subgroups in duality groups and in groups of
cohomological dimension 2*, J. Pure Appl. Algebra 7 (1976) 35–51. It was not
read.

**Argument.** `N` is neither free nor of finite index, so it is not finitely
presented. `N` is finitely generated, so `SL_3(Z)` is incoherent.

**Trust boundary.**

- The hypothesis range of Bieri's theorem was checked only through the
  quotation, which puts no finiteness condition on `G`.
- If the original needs `G` of type `FP_2` or `FP`, this route needs that
  hypothesis too.
- The fibred instance satisfies it (`G` of type FP).

Relation to other routes. `sl3z-incoherent-via-euler-fibered-subgroup` proves
the fibred special case without Bieri, through the Wang sequence.
