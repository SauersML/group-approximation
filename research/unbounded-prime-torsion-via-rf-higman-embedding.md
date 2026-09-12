---
rg: 2
id: unbounded-prime-torsion-via-rf-higman-embedding
kind: route
title: A residually finite Higman embedding of the cycle-transposition group yields unbounded prime torsion
target: fp-rf-group-with-unbounded-prime-torsion
requires:
  - rf-higman-embedding-for-decidable-groups
  - cycle-transposition-lef-group-has-no-regular-tree-action
---

By `cycle-transposition-lef-group-has-no-regular-tree-action`, the group
`Gamma` there has these properties:
- it is finitely generated and residually finite;
- it has solvable word problem;
- it has elements of every prime order `p >= 5`.

So `rf-higman-embedding-for-decidable-groups` embeds `Gamma` in a finitely
presented residually finite group `G`. The elements of prime order lie in `G`.
`∎`
