---
rg: 2
id: simple-kazhdan-lef-host-for-countably-many-rf-groups-proof
kind: route
title: Direct sum, Wilson's 2-generator residually finite overgroup, then the simple Kazhdan LEF envelope
target: simple-kazhdan-lef-host-for-countably-many-rf-groups
requires:
  - wilson-countable-rf-into-two-generator-rf-groups
  - rf-groups-embed-in-simple-kazhdan-lef-groups
artifacts:
  - research/artifacts/sk-strong-3-universal-host-2026-09-13.md
---

Let `F = {Γ_1, Γ_2, …}`.

1. **Direct sum.** `P = ⊕_i Γ_i` is countable and residually finite. For `p ≠ e`, choose `i` with `p_i ≠ e` and a
   finite quotient of `Γ_i` in which `p_i` survives, and compose it with the projection `P -> Γ_i`. Each `Γ_i` embeds
   in `P` as a coordinate.
2. **Two generators.** By `wilson-countable-rf-into-two-generator-rf-groups` (Wilson 1980, Theorem A), `P` embeds in a
   2-generator residually finite group `W`.
3. **Envelope.** By `rf-groups-embed-in-simple-kazhdan-lef-groups`, `W` embeds in an infinite, finitely generated,
   simple group `S` with property (T) that is LEF. That result covers finite `W` by replacing `W` with `W × Z`.
4. So `Γ_i ≤ P ≤ W ≤ S` for every `i`. ∎

The claim node gives the countability of the example classes in Corollary U′. The artifact gives sharpness and credit.
