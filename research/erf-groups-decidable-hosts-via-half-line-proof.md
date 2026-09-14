---
rg: 2
id: erf-groups-decidable-hosts-via-half-line-proof
kind: route
title: Effectively residually finite groups are LEF, so the half-line lamplighter host with solvable word problem contains them
target: erf-groups-have-decidable-simple-kazhdan-hosts
requires: [lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts]
artifacts:
  - research/artifacts/sk-decidable-host-2026-09-13.md
---

Let `Γ` be finitely generated, infinite, effectively residually finite, with solvable word problem.
- A finitely generated residually finite group is LEF: the finite quotients injective on a ball are finite models.
- `lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts` embeds `Γ` in an infinite, finitely generated, simple
  Kazhdan LEF group with solvable word problem.

That is the target statement. Effective residual finiteness is not used, only residual finiteness and the solvable
word problem. The overgroup the target node was missing (`Γ ≤ [Δ,Δ]` with `Δ` computable) is `C(Γ)`, which is LEF
but not residually finite for non-abelian `Γ`. Artifact §5.
