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

By `cycle-transposition-lef-group-has-no-regular-tree-action`, the group `Gamma` there:
- is finitely generated and residually finite;
- has solvable word problem;
- has elements of every prime order `p >= 5`.

So `rf-higman-embedding-for-decidable-groups` embeds `Gamma` in a finitely presented residually finite group `G`, and the elements of prime order lie in `G`. `∎`

**Status of the premise (2026-09-13).** `rf-higman-embedding-for-decidable-groups` is refuted in general: Rauzy, arXiv:2002.02540, Theorem 1 (`rf-higman-embedding-for-decidable-groups-fails`). So this route is dead as written.
- The same conclusion would follow from a finitely presented residually finite overgroup of `Gamma` alone.
- Rauzy's obstruction does not exclude such an overgroup, since `Gamma` is effectively residually finite.
