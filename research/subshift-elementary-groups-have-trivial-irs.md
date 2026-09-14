---
rg: 2
id: subshift-elementary-groups-have-trivial-irs
kind: claim
title: Every invariant random subgroup of EL_3(LC(X,F_2)⋊Z) is a mixture of the trivial subgroup and the whole group
artifacts:
  - research/artifacts/sk-characters-rigidity-b-proof-2026-09-13-part2.md
  - research/artifacts/leavitt-irs-rigidity-from-character-simplex-2026-09-08.md
---

**ESTABLISHED (unreviewed).** Let `X` be an infinite minimal subshift and `G_X = EL_3(LC(X,F_2) ⋊ Z)`. Then

`IRS(G_X) = {(1−b)δ_{1} + b δ_{G_X} : 0 ≤ b ≤ 1}`.

So every probability-preserving action of `G_X` is essentially free off its set of global fixed points.

Route: `subshift-elementary-groups-have-trivial-irs-proof`.

**Review (sk-verify-8, 2026-09-13, `research/artifacts/sk-review-8-2026-09-13-part2.md`):** PASS (§3). The character-simplex principle is re-derived with a lazy fully supported random walk: `∫ν^{*n}(H)dμ → μ({G})`, return probabilities vanish on infinite Schreier graphs, and `G_X` has no proper finite-index subgroup. So `μ({G}) = b`, and countability gives `μ = bδ_G + (1−b)δ_1`.
