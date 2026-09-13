---
rg: 2
id: strict-comparison-unit-divisibility-equivalences-proof
kind: route
title: Rordam-Winter Proposition 5.1 with strict comparison replacing stable rank one, plus rank bookkeeping and a dimension drop order zero map
target: strict-comparison-unit-divisibility-equivalences
requires: []
artifacts:
  - research/artifacts/ex-toms-winter-unit-divisibility-equivalences-2026-09-12.md
  - research/artifacts/ex-toms-winter-bauer-divisible-unit-part2-2026-09-12.md
---

**Direct proof**, Proposition 1 of the first artifact.

**Import.** Rørdam–Winter, arXiv:0801.2259, Proposition 5.1, read on MSI (lines
469–545). For unital `A`, condition (ii) ("There exist ε > 0 and mutually equivalent
and orthogonal positive elements b1, …, bn in A such that
1_A − (b1 + ··· + bn) ≾ (b1 − ε)_+") implies (iv) ("There is a unital ∗-homomorphism
from the C∗-algebra Z_{n,n+1} into A"). "The hypothesis of stable rank one is only
needed for the implication (i) ⇒ (ii)."

1. **2 ⇒ 3.** Order zero `φ: M_L → A` with trace above `1 − ε`, and `r` with
   `1/(n+1) < r/L < 1/n`. Then `x_0 = φ(e_11 + ··· + e_rr)` has
   `d_τ(x_0) ≤ r/L < 1/n` and `d_τ(x_0) ≥ τ(x_0) > 1/(n+1)`. Strict comparison gives
   `n[x_0] ≤ [1] ≤ (n+1)[x_0]`.
2. **4 ⇒ 3.** `z = m x` with an integer `m ∈ [(L+1)/(n+1), L/n]`, which exists once
   `L ≥ n(n+1) + n`.
3. **3 ⇒ 5.**
   - At level `3n+1`, `z = 3y` has `n z ≤ [1]` and `d_τ(z) ≥ 3/(3n+2) > 1/(n+1)`.
   - Compactness of `T(A)` and lower semicontinuity give `δ` with
     `d_τ((d − δ)_+) > 1/(n+1)`.
   - Rørdam's lemma gives a row `t` with `t*t = ⊕^n (d − δ/2)_+`. The `e_j = t_jt_j*`
     are orthogonal.
   - With a cutoff `f` vanishing on `[0, δ/4]` and equal to `1` on `[δ/2, 1]`, the
     elements `b_j = f(e_j)` are mutually equivalent through `x_j = t_j m(g) t_1*`,
     where `m(t) = f(t)^{1/2}/t` is bounded.
   - Then `d_τ(1 − Σ b_j) ≤ 1 − n d_τ((d − δ)_+) < d_τ((d − δ)_+) ≤ d_τ((b_1 − ε')_+)`.
     Strict comparison gives (ii), hence (iv).
4. **6 ⇒ 1.** Lemma 3.2 of the part 2 artifact: an order zero `M_N → Z_{n,n+1}` with
   `tr(ψ(1)(t)) ≥ 1 − N/n` at every `t`. Every trace of `A` restricts to an integral
   of fibre traces.
5. **Trivial.** 1 ⇒ 2, 3 ⇒ 4 and 5 ⇒ 6. ∎
