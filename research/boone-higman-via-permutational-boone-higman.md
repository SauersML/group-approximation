---
rg: 2
id: boone-higman-via-permutational-boone-higman
kind: route
title: Place every decidable input inside a type (A) actor and take its twisted Brin-Thompson group
target: boone-higman-conjecture
requires:
  - permutational-boone-higman-conjecture
  - type-a-action-gives-boone-higman-for-subgroups
---

Let `G` be finitely generated with solvable word problem.
1. By `permutational-boone-higman-conjecture`, `G <= Gamma` for some `Gamma`
   admitting an action of type (A).
2. By Zaremsky's Corollary B, imported as
   `type-a-action-gives-boone-higman-for-subgroups`, every subgroup of `Gamma`
   embeds in the finitely presented simple group `SV_Gamma`.

So `G` embeds in a finitely presented simple group.

The other direction is `permutational-boone-higman-via-mif-envelopes`, and it
needs the extra hypothesis `fp-simple-groups-embed-in-fp-simple-mif-groups`.
So the two routes form a cycle through the pair of conjectures. The cycle is
intended: it records a conditional equivalence, and neither route fires unless
an open premise is proved.
