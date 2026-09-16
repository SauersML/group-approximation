---
rg: 2
id: strict-comparison-property-tm-forces-sr1
kind: claim
title: Under strict comparison, property (TM) is equivalent to stable rank one (Fu-Lin)
distinct_from:
  strict-comparison-rank-surjectivity-forces-sr1: that is Lin's 2023 theorem, whose hypothesis is surjectivity of the rank map; this is the earlier Fu-Lin theorem, whose hypothesis is the order zero tracial property (TM), the form that tracial divisibility reaches.
  stable-rank-one-unital-algebras-are-k1-bijective: that is Rieffel's consequence of stable rank one; this produces stable rank one.
artifacts:
  - research/artifacts/stw18-k1-witness-tracial-divisibility-2026-09-16.md
---

Let `A` be a separable simple C*-algebra with at least one densely defined
non-trivial 2-quasitrace. Assume `A` has strict comparison: for
`a, b ∈ (A⊗K)_+`, `a ≲ b` whenever `d_τ(a) < d_τ(b)` for all
`τ ∈ QT~(A) \ {0}`. Then the following are equivalent:

1. `A` has tracial approximate oscillation zero;
2. `Γ` is surjective and `A` has stable rank one;
3. `A` has stable rank one;
4. `Γ` is surjective and `A` has almost stable rank one;
5. `A` has property (TM).

Nuclearity and exactness are not assumed.

**Property (TM).**

- **Relative to a compact `S ⊂ QT~(A) \ {0}`.** For all `a ∈ Ped(A⊗K)_+`,
  `ε > 0` and `n` there is a c.p.c. order zero `φ: M_n → Her(a)` with
  `sup_{τ∈S} τ((a − φ(1_n)a)*(a − φ(1_n)a))^{1/2} < ε`.
- **For σ-unital simple `A`.** Some `e ∈ Ped(A)^1_+ \ {0}` has `Her(e)` with
  property (TM) relative to the weak* closure of
  `QT(A) = {τ : ‖τ|_A‖ = 1}`.
