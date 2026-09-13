---
rg: 2
id: braid-groups-have-no-nontrivial-kazhdan-subgroups-proof
kind: route
title: Pure braid groups are locally indicable, and braid groups are torsion-free
target: braid-groups-have-no-nontrivial-kazhdan-subgroups
requires: []
artifacts:
  - research/artifacts/zp-braid-haagerup-fences-2026-09-13-part2.md
---

A group is locally indicable if every nontrivial finitely generated subgroup surjects onto `Z`. Free groups
are locally indicable, and an extension of a locally indicable group by a locally indicable group is locally
indicable. (A nontrivial f.g. subgroup either has nontrivial image in the quotient, or lies in the kernel.)
Artin combing `P_n ≅ F_{n−1} ⋊ P_{n−1}` and induction from `P_1 = 1` show that `P_n` is locally indicable.

A countable group with property (T) is finitely generated with finite abelianization, so every (T) subgroup
of `P_n` is trivial. If `H ≤ B_n` has (T), then `H ∩ P_n` has finite index in `H`, inherits (T), and is
trivial. So `H` is finite, and `H = 1` because `B_n` is torsion-free (it has a finite-dimensional
`K(B_n, 1)`, the unordered configuration space of `n` points in the plane).

Full text: §1 of `research/artifacts/zp-braid-haagerup-fences-2026-09-13-part2.md`.
