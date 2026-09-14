---
rg: 2
id: lef-iff-simple-kazhdan-finite-simple-limit-proof
kind: route
title: Ore overgroup, commutator embedding into the lamplighter host, and the host's finite simple limits
target: lef-iff-subgroup-of-simple-kazhdan-finite-simple-limit
requires: [rf-groups-lie-in-derived-subgroups-of-rf-groups, lamplighter-bernoulli-crossed-products-simple-kazhdan-lef, lamplighter-host-is-limit-of-finite-simple-expanders]
artifacts:
  - research/artifacts/sk-strong-8-finite-simple-limits-2026-09-13.md
---

Full derivation: artifact §3, proof of Theorem B.

- **(1) ⇒ (2).**
  - Replace a finite Γ by Γ × Z.
  - By `rf-groups-lie-in-derived-subgroups-of-rf-groups` (LEF part), `Γ ≤ [Δ,Δ]` with `Δ` finitely generated, infinite and LEF.
  - Then `[Δ,Δ] ≤ [L,L]`, and `γ ↦ diag(u_γ,1,1)` embeds `[L,L]` in `H = EL_3(LC(2^Δ,F_2)⋊L)` (item 4 of `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef`).
  - `H` is a marked limit of finite simple expanders by `lamplighter-host-is-limit-of-finite-simple-expanders`.
- **(2) ⇒ (1).**
  - A marked limit of finite groups is LEF, because balls inject into approximants preserving products inside the ball.
  - Finitely generated subgroups of LEF groups are LEF.
