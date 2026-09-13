---
rg: 2
id: some-lo-simple-type-f-group-contains-thompson-like-subgroups
kind: claim
title: "Some left-orderable simple group of type F contains F' or Z wreath Z, or acts on the line with arbitrarily many disjointly supported elements"
refuted_by: finite-cd-line-groups-bound-disjointly-supported-families
---

The premise of the natural Thompson-like attack on Zaremsky Problem 1.22: upgrade a Thompson-like
left-orderable simple group, such as the Hyde–Lodha groups `G_ρ`, or build an overgroup of one, to reach
type F.

Stated as: there is a left-orderable simple group `G` of type F such that either
- `G` contains a copy of `F' = [F,F]` or of `Z ≀ Z`, or
- `G` acts faithfully on `R` so that, for every `n`, some `n` nontrivial elements have pairwise disjoint
  supports.

**Refuted** by `finite-cd-line-groups-bound-disjointly-supported-families`. Each alternative forces free
abelian subgroups of every rank, hence infinite cohomological dimension, while type F forces finite
cohomological dimension.

## Attempts

- 2026-09-13 (z1-22-lo-simple-thompson): refuted as recorded above. The Hyde–Lodha groups contain `F'`
  (`hyde-lodha-groups-contain-thompson-commutator-subgroup`), so no overgroup of theirs can be of type F.
