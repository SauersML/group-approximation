---
rg: 2
id: subshift-elementary-groups-have-trivial-irs-proof
kind: route
title: Trivial invariant random subgroups from the two-point character simplex and simplicity
target: subshift-elementary-groups-have-trivial-irs
requires: [subshift-elementary-groups-are-character-rigid, simple-kazhdan-lef-group-from-minimal-subshift]
artifacts:
  - research/artifacts/leavitt-irs-rigidity-from-character-simplex-2026-09-08.md
---

The general principle is in `research/artifacts/leavitt-irs-rigidity-from-character-simplex-2026-09-08.md` §1–§2: the lazy return limit identifies the mass `b = μ({G})`. It applies to every countably infinite group `G` such that:
1. `G` has no proper subgroup of finite index;
2. every normalized positive definite class function is `b·1 + (1−b)δ_1`.

For `G_X`:
- (1) holds because `G_X` is infinite and simple (`simple-kazhdan-lef-group-from-minimal-subshift`), so a finite-index subgroup contains the normal core, which is `G_X`;
- (2) is `subshift-elementary-groups-are-character-rigid`, in its stronger form proved by `subshift-elementary-groups-character-rigid-proof`.

The principle then gives `IRS(G_X) = {(1−b)δ_{1} + bδ_{G_X}}`.
