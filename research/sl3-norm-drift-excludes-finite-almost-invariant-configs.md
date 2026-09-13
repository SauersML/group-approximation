---
rg: 2
id: sl3-norm-drift-excludes-finite-almost-invariant-configs
kind: claim
title: Elementary matrices push the operator norm up on average, so no finite configuration in SL3(R) is almost invariant under them, even with a small fraction of defects
artifacts:
  - research/artifacts/sl3z-cocompact-quotient-holonomy-drift-2026-09-13.md
---

**ESTABLISHED.** Let `S = {e_ij^(±1)}` be the 12 elementary matrices of `SL_3(Z)`, with `||·||` the
Euclidean operator norm.

1. **Drift.** For every `x ∈ SL_3(R)`, `Σ_(s ∈ S) log||sx|| >= 12 log||x|| + κ`, where
   `κ = (1/2) log(128/81) > 0`.
2. **Finite configurations.** Let `O` be a finite set with bijections `τ_s : O → O` (`s ∈ S`) and a map
   `Φ : O → SL_3(R)`. Suppose `log||Φ(τ_s ω)|| >= log||sΦ(ω)|| − B` for all pairs `(ω,s)`, and
   `log||Φ(τ_s ω)|| >= log||sΦ(ω)|| − η` for all but a proportion `θ` of the `12|O|` pairs. Then
   `κ <= 12(η + θB)`.

In metric form, with a right-invariant metric `d` on `SL_3(R)`: an almost-equivariance defect
`d(Φ(τ_sω), sΦ(ω)) < ε` costs at most `η(ε) → 0`, and a defect `<= D` costs at most `B(D)`.

No relations among the `τ_s` and no freeness are assumed. The mechanism is that the norm drifts
upward on average, while bijections of a finite set preserve every sum. It is a quantitative form
of the statement that `SL_3(Z)` has no finite almost-invariant configurations in `SL_3(R)`.

Proof in `sl3-norm-drift-excludes-finite-almost-invariant-configs-proof`.
