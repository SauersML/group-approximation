---
rg: 2
id: simple-lef-groups-are-limits-of-finite-simple-groups-proof
kind: route
title: Quotient approximants by maximal normal subgroups, and use ultraproducts plus Mal'cev for the rank bound
target: simple-lef-groups-are-limits-of-finite-simple-groups
requires: []
artifacts:
  - research/artifacts/sk-free-4-finite-simple-shadows-2026-09-13-part1.md
---

Direct proof, in full in the artifact §§2–3.
- **Relators survive** in quotients.
- **Nonrelators survive.** For each nontrivial word `w` of length `≤ r` and generator `t`, simplicity gives a relator
  `c_(w,t) = t^(-1)∏ h_i w^(ε_i) h_i^(-1)`. For large `k` the relators `c_(w,t)` hold in `Q_k`. So `w ∈ M_k` would give
  `Q_k ⊆ M_k`.
- **Nonabelian.** A nontrivial commutator of generators survives, so `Q_k/M_k` is nonabelian.
- **Rank.** Along an ultrafilter, `F(T) → ∏_ω Q_k` has kernel exactly the relators of `G`, so `G` embeds. If
  `Q_k ≤ GL_d(K_k)` infinitely often, then `∏_ω Q_k ≤ GL_d(∏_ω K_k)` is linear over a field (Łoś). Mal'cev's theorem
  makes `G` residually finite, which contradicts infinite simplicity.
- **Classification step.** Groups of Lie type of rank `ℓ` embed in `GL_(c(ℓ))` of a field, and there are finitely many
  sporadic groups.
