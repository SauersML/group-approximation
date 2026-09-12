---
rg: 2
id: leavitt-path-simultaneous-division-proof
kind: route
title: Push supports to a base vertex, separate blocks by length, make an antichain with a cycle exit, and transport the unit into the base vertex
target: leavitt-path-algebras-have-simultaneous-strong-division
requires: []
artifacts:
  - research/artifacts/bh-leavitt-path-steinberg-hosts-2026-09-12.md
---

Direct proof. It uses CK1, CK2, linear independence of paths in `L_K(E)`, and
the stated graph conditions. Full text: artifact Section 2.

**Setup.** Fix a cycle `C` based at `c_0`, an exit `ε` from a vertex `x` of `C`,
the arc `α` of `C` from `c_0` to `x` (`|α| < |C|`), and a path `ρ` from `r(ε)` to
`c_0`. `ρ` exists by cofinality.

1. **Path algebra.** Choose `N` bounding every `|μ|` in `a_i = Σ c λ μ*`. No sinks
   gives `1 = Σ_(|γ|=N) γγ*`. Each `a_i γ` is a combination of real paths ending
   at `r(γ)`, and some `a_i γ != 0`.
2. **Blocks.** Choose paths `τ_γ` from `r(γ)` to `c_0` (lengths `d + k|C|`) with
   pairwise disjoint length windows, and put `x_0 = Σ_γ γ τ_γ`.
   - `P_i = a_i x_0 = Σ_γ (a_i γ) τ_γ` has no cancellation, so `P_i != 0`.
   - All support paths of `P_i` end at `c_0`.
3. **Antichain.** Put `τ = C^k α ε ρ` with `k|C|` larger than every support length.
   - Distinct support paths `ν, ν'` give incomparable `ντ, ν'τ`: equal lengths
     differ early. If `|ν| < |ν'|`, the edge `ε` of `ντ` sits inside the `C^k α`
     block of `ν'τ`, whose edges lie in `C`.
   - Taking `η_i` in the support of `P_i τ` with coefficient `c_i` gives
     `η_i* a_i x_0 τ = c_i c_0`.
4. **Unit transport.** Take `M >= |E^0|`. Every length-`M` path `γ` passes through a
   cycle vertex, so `c_0` reaches `r(γ)` by some `μ_γ`, using cofinality.
   - The loops `π_j = C^j α ε ρ` at `c_0` are pairwise incomparable.
   - `S = Σ_j π_j μ_(γ_j) γ_j*` satisfies `S = c_0 S` and `S* S = 1`, so
     `S* c_0 S = 1`.
5. **Assemble.** `X = x_0 τ S` and `u_i = c_i^(-1) S* η_i*` give `u_i a_i X = 1`. `∎`
