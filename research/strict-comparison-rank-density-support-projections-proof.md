---
rg: 2
id: strict-comparison-rank-density-support-projections-proof
kind: route
title: Select a near projection of profile (1 − ε)τ(a), move its cut-down under a by strict comparison and Rørdam's lemma, and transport it through c*c ~ cc*
target: strict-comparison-with-rank-density-gives-support-projections
requires: []
artifacts:
  - research/artifacts/tw-support-gap-crux-2026-09-12.md
---

Complete proof: Section 1 of `research/artifacts/tw-support-gap-crux-2026-09-12.md`.

**Constants.** Fix `a ≠ 0` and put `c = min_τ τ(a) > 0`. For `ε ∈ (0,1/4)` put
`δ = ε/4` and `η = εcδ/8`.

1. **Profile.** RD_b gives a positive contraction `q ∈ M_k(A)` with
   `|τ(q) − (1−ε)τ(a)| < η` and `τ(q − q²) < η`.
2. **Rank gap.** `μ_τ((δ,1−δ)) ≤ 2η/δ` and `μ_τ([1−δ,1]) ≤ τ(q)/(1−δ)`. So
   `d_τ((q−δ)_+) ≤ τ(a) − 3εc/4 + 4η/δ < τ(a) ≤ d_τ(a)`.
3. **Comparison.** Strict comparison gives `(q−δ)_+ ≾ a`. Choose `r` with
   `‖(q−δ)_+ − rar*‖ < δ`. Rørdam's lemma gives a contraction `d` with
   `drar*d* = (q−2δ)_+`.
4. **Transport.** Put `c_0 = dra^{1/2}`. Then `c_0c_0* = (q−2δ)_+` and
   `c_0*c_0 ∈ closure(a M_k(A) a)`.
5. **The near projection.** Take `ψ(s) = min(1, s/(1−4δ))` and `b = ψ(c_0*c_0)`.
   By the trace identity, `τ(b) = τ(φ(q))` and `τ(b−b²) = τ(φ(q)−φ(q)²)`, where
   `φ(t) = ψ((t−2δ)_+)`.
6. **Estimates.** `τ(b − b²) ≤ η/(4δ) ≤ εk` and `τ(b) ≥ τ(a) − 3εk`. So
   `γ_A(a) ≤ 3εk` for every `ε`.
