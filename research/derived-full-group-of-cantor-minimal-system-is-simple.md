---
rg: 2
id: derived-full-group-of-cantor-minimal-system-is-simple
kind: claim
title: "Matui: for a Cantor minimal system the commutator subgroup D([[ϕ]]_0) of the topological full group is simple, by localization to alternating groups on towers"
artifacts:
  - research/artifacts/sk-novelty-prior-art-2026-09-13-part2.md
---

For every Cantor minimal system `(X,ϕ)`, the commutator subgroup `D([[ϕ]]_0)` is simple, in the notation of Matui §4
(Internat. J. Math. 17 (2006), Theorem 4.9).

**The proof localizes.**
- Take a nontrivial element `γ` of a normal subgroup `N`.
- Let `σ` be the involution that is `ϕ` on a small clopen set `U` (with `U ∩ ϕ(U) = ∅`), `ϕ^{-1}` on `ϕ(U)`, and the
  identity elsewhere.
- The commutator `σγ^{-1}σγ` is nontrivial and lies in `D([[ϕ]]_x)`.
- `D([[ϕ]]_x)` is the commutator subgroup of an AF full group: an increasing union of direct sums of alternating groups
  `A_{h(v)}` on Kakutani–Rokhlin towers. It is simple (Lemma 3.4), so `N ⊇ D([[ϕ]]_x)`.

**Credit note for `simple_kazhdan_sofic_group.tex`.** Its simplicity step for `EL_3(LC(X,F_2) ⋊ Z)` follows the same
localization, with the finite simple group `GL_d(F_2)` on a clopen tower in place of alternating groups
(`research/artifacts/sk-novelty-proposal-2026-09-13.md`, P1).
