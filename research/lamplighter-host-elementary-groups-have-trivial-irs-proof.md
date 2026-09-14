---
rg: 2
id: lamplighter-host-elementary-groups-have-trivial-irs-proof
kind: route
title: Trivial invariant random subgroups of the lamplighter hosts from the two-point character simplex and simplicity
target: lamplighter-host-elementary-groups-have-trivial-irs
requires: [lamplighter-host-elementary-groups-are-character-rigid, binary-el-simple-iff-minimal-topologically-free]
artifacts:
  - research/artifacts/leavitt-irs-rigidity-from-character-simplex-2026-09-08.md
---

The principle of `research/artifacts/leavitt-irs-rigidity-from-character-simplex-2026-09-08.md` §1–§2 applies to a countable group with:
1. no proper subgroup of finite index;
2. every character equal to `b·1 + (1−b)δ_1`.

This is the same principle as `subshift-elementary-groups-have-trivial-irs-proof`, which sk-verify-8 passed.

For `G_Δ`:
- (1): `Λ ↷ Ω` is minimal (orbits contain `x + ⊕_Δ F_2`, which is dense) and topologically free (the fixed-point equation, rev4 §3). So `G_Δ` is simple by `binary-el-simple-iff-minimal-topologically-free`. Since `Δ` is infinite, `G_Δ` is infinite, and a finite-index subgroup contains its normal core, which is `G_Δ`.
- (2) is `lamplighter-host-elementary-groups-are-character-rigid`.
