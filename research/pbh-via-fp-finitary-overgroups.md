---
rg: 2
id: pbh-via-fp-finitary-overgroups
kind: route
title: Embed every decidable input in a finitely presented overgroup of the finitary alternating group and use its natural action
target: permutational-boone-higman-conjecture
requires:
  - decidable-groups-embed-in-fp-finitary-overgroups
  - fp-finitary-permutation-overgroups-are-type-a-actors
---

Let `G` be finitely generated with solvable word problem.

1. By `decidable-groups-embed-in-fp-finitary-overgroups`, `G <= Gamma` with
   `Gamma` finitely presented and `Alt_fin(X) <= Gamma <= Sym(X)` for a
   countably infinite `X`.
2. By items 1--3 of `fp-finitary-permutation-overgroups-are-type-a-actors`,
   the natural action `Gamma ↷ X` is faithful, has two orbits of ordered pairs
   and finitely generated point stabilizers. Since `Gamma` is finitely
   presented, this action is of type (A).

So `G` lies in a group with a type (A) action, which is the conclusion of
permutational Boone--Higman for `G`.

**Decomposition.** Together with `boone-higman-via-permutational-boone-higman`,
this reduces Boone--Higman to the single open prerequisite of finite
presentation for finitary overgroups. It uses no HNN extensions and no
decidable edge groups. The other hypotheses of type (A) are established, so
they cannot fail. What can fail is recorded under the prerequisite's
necessary conditions.
