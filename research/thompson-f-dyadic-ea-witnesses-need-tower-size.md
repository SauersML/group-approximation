---
rg: 2
id: thompson-f-dyadic-ea-witnesses-need-tower-size
kind: claim
title: Approximate extensive-amenability witnesses for F on the dyadics need a tower of exponentials of sets or of points per set
distinct_from:
  thompson-f-folner-function-exceeds-every-tower: that is Moore's lower bound for Følner sets of F; this transfers it to approximately invariant measures on finite subsets of the dyadics that cover the generators' breakpoints.
  thompson-f-cardinality-certificates-need-tower-degree: that transfers Moore's bound to monomial doubling certificates in the group ring; this transfers it to extensive-amenability witnesses.
  thompson-f-amenable-iff-dyadic-action-extensively-amenable: that is the qualitative equivalence; this is its quantitative form.
  f-dyadic-inverted-orbit-is-subballistic-on-rare-events: that is the open confinement target; this bounds below the size of any finite witness for it, without deciding it.
---

**ESTABLISHED** through `thompson-f-dyadic-ea-witnesses-need-tower-size-proof` (direct proof from Moore's
theorem and `thompson-f-amenable-iff-dyadic-action-extensively-amenable`; not independently reviewed; no
priority claimed).

Let `Γ ⊆ F` be a finite symmetric generating set and `C > 1` Moore's constant for `Γ`
(`thompson-f-folner-function-exceeds-every-tower`). For `s ∈ F` let `B(s) ⊂ D` be its set of breakpoints and
`β(s) ∈ Z^{(D)}` its log₂-slope jumps. Put `L = Σ_{s∈Γ} ‖β(s)‖₁`, and `exp_0(n) = n`,
`exp_{p+1}(n) = 2^{exp_p(n)}`.

**Theorem.** Let `ν` be a finitely supported probability measure on the finite subsets of `D`. Put
`k = max{|S| : S ∈ supp ν}` and

- `ε₁ = Σ_{s∈Γ} ‖sν − ν‖₁`, where `(sν)(T) = ν(s⁻¹T)`;
- `ε₂ = Σ_{s∈Γ} Σ_{y∈B(s)} ν{S : y ∉ S}`.

If `ε₁ + 2ε₂ < C^{−n}/2` for some `n ≥ 1`, then `|supp ν| · (4LC^n + 3)^k ≥ exp_n(0)`.

**Reading.** An extensively amenable mean for `F ↷ D` is a weak* limit of such `ν` with `ε₁ → 0` and
`ν{S : y ∉ S} → 0` for each `y`. The theorem only needs invariance under `Γ` and coverage of the finitely
many breakpoints of `Γ`. At invariance level `C^{−n}`, either `log₂|supp ν| ≥ exp_{n−1}(0)/2`, or
`k ≥ exp_{n−1}(0) / (2 log₂(4LC^n + 3))`. So a witness needs tower-size support or tower-size sets.

**Class killed.** No witness family for `thompson-f-dyadic-action-is-extensively-amenable` has size
`|supp ν| · 2^k ≤ exp_p((1/ε)^d)` for a fixed height `p` and degree `d`, where `ε = ε₁ + 2ε₂`. With
`1/ε ≈ 2C^n`, the right-hand side is eventually below `exp_n(0)`. This covers, for example, laws of sets
built from `m`-step words (`|supp ν| ≤ |Γ|^m`, `k ≤ m+1`) with `m` bounded by a fixed-height tower in `1/ε`.
Such a family would yield Følner sets of `F` of that size, which Moore's theorem excludes. The obstruction
is sharp only as far as Moore's bound is: it says nothing about witnesses of tetration size.
