---
rg: 2
id: lamplighter-host-elementary-groups-have-trivial-irs
kind: claim
title: Every invariant random subgroup of EL_n over the lamplighter crossed product of an infinite group is a mixture of the trivial subgroup and the whole group
distinct_from:
  subshift-elementary-groups-have-trivial-irs: that is the Z-subshift groups G_X; this is the lamplighter hosts G_Δ of the LEF characterization, for every infinite Δ.
artifacts:
  - research/artifacts/sk-lamplighter-characters-2026-09-14-part2.md
  - research/artifacts/leavitt-irs-rigidity-from-character-simplex-2026-09-08.md
---

**ESTABLISHED (unreviewed).** Let `Δ` be an infinite countable group, `Λ = F_2 ≀ Δ ↷ Ω = F_2^Δ`, and `G_Δ = EL_n(LC(Ω,F_2) ⋊ Λ)`, `n ≥ 3`. Then

`IRS(G_Δ) = {(1−b)δ_{1} + b δ_{G_Δ} : 0 ≤ b ≤ 1}`,

so every probability-preserving action of `G_Δ` is essentially free off its global fixed set.

Route: `lamplighter-host-elementary-groups-have-trivial-irs-proof`.

## Review
- **sk-verify-18 PASS (2026-09-14, `research/artifacts/sk-verify-18-2026-09-14-part9.md`):** minimal and topologically free, so G_Δ is simple by the binary criterion, with no finite generation needed. It is infinite, so it has no proper finite-index subgroup. With the two-point character simplex, the IRS principle gives the trivial IRS.
