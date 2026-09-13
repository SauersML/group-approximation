---
rg: 2
id: measure-rf-property-passes-to-subgroups
kind: claim
title: The class of groups all of whose full-support invariant-measure Cantor actions are residually finite is closed under subgroups and finite-index overgroups
artifacts:
  - research/artifacts/un-rf-beyond-free-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Say `Γ ∈ 𝔑` if every continuous `Γ`-action on a Cantor space admitting an invariant
Borel probability measure of full support is residually finite (Kerr–Nowak). Then:
1. if `Γ ∈ 𝔑` and `H <= Γ`, then `H ∈ 𝔑`;
2. if `H <= Γ` has finite index and `H ∈ 𝔑`, then `Γ ∈ 𝔑`.
So `𝔑` is a commensurability invariant.

Proof of 1: co-induce the `H`-action to `Y^(Γ/H)` with product measure, restrict the RF `Γ`-action back to `H`,
and pass to the coordinate factor `f ↦ f(e)`. Proof of 2: `rf-actions-induce-from-finite-index-subgroups`.

Route: `measure-rf-property-passes-to-subgroups-proof`.
