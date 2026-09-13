---
rg: 2
id: pbh-via-orbit-finite-affine-actors
kind: route
title: Embed each decidable input in an orbit-finite affine actor and use the affine type (A) criterion
target: permutational-boone-higman-conjecture
requires:
  - decidable-groups-embed-in-orbit-finite-affine-actors
  - orbit-finite-affine-actions-are-type-a
---

Let `G` be finitely generated with solvable word problem. By
`decidable-groups-embed-in-orbit-finite-affine-actors` there are a countable group
`S` and a finitely generated `W <= Aut(S)` with finitely many orbits on `S`, such
that `Γ = S ⋊ W` is finitely presented and contains `G`. By
`orbit-finite-affine-actions-are-type-a`, item 3, the affine action of `Γ` on `S` is
faithful and of type (A). So `G` embeds in a group admitting an action of type (A),
which is the statement of `permutational-boone-higman-conjecture`.
