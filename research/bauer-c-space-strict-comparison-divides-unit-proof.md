---
rg: 2
id: bauer-c-space-strict-comparison-divides-unit-proof
kind: route
title: Screen local divisions by property C, switch them on with central staircases, and orthogonalize the levels by strict comparison
target: bauer-c-space-strict-comparison-divides-unit
requires:
  - strict-comparison-unit-divisibility-equivalences
artifacts:
  - research/artifacts/ex-tw-c-space-unit-division-2026-09-13.md
  - research/artifacts/ex-tw-c-space-unit-division-part2-2026-09-13.md
---

Full proof: Sections 0–2 of the first artifact and Section 3 of part 2.

**Inputs.**
- Ozawa, arXiv:1304.3523, Theorem 3, read on MSI by lane `ex-toms-winter`. It gives a
  central `θ: C(K) → A^st` with `λ(θ(f)x) = f(λ)λ(x)` at extreme traces.
- Rørdam's lemma, the Winter–Zacharias structure theorem and order zero lifting. These
  are standard and were not re-read.
- The only graph input is `strict-comparison-unit-divisibility-equivalences`, item 3 ⟹ item 1.

**Steps.** Fix `n`, the midpoint `t` of `(1/(n+1), 1/n)`, and `ε` of a quarter of that
interval's length.
1. **Lemma 1.** Every `λ_0 ∈ K` has a neighbourhood with an order zero
   `φ: M_N → A` such that `λ(1 − φ(1)) < δ` there.
2. **Screening.**
   - Choose precisions with `Σ_k (6 d_k^{1/2} + δ_k) ≤ ε/2`, where `d_k = 1/(4N_k) + δ_k`.
   - Property C and compactness give levels `k ≤ L` of disjoint open families.
   - Lemma 2 combines each family into one order zero `φ_k: M_{N_k} → A^st` through
     disjointly supported central cutoffs.
   - Take a partition of unity `h_k` with `φ_k` good on `supp h_k`.
3. **Lemma 3 (staircase).**
   - Put `B_k = Σ_{j ≤ ⌈N_k t⌉} θ(clamp(N_k t h_k − j + 1)) φ_k(e_jj)`.
   - `B_k` is zero in the fibre where `h_k = 0`.
   - `t h_k − δ_k ≤ λ(B_k) ≤ t h_k`, and `λ(B_k − B_k²) ≤ 1/(4N_k) + δ_k`.
   - Approximate `B_k` by a positive contraction `b_k ∈ A` within `η` in `‖·‖_{2,u}`,
     with `η` chosen after `L`.
4. **Rank bounds.** Put `s_k = d_k^{1/2}` and `x_k = (b_k − s_k)_+`. For `σ ≥ s_k`,
   `μ_{b_k,λ}((σ,1])` lies in `[t h_k − δ_k − η − σ, t h_k + 6 s_k + 8η/s_min]` at every
   extreme `λ`.
5. **Moves.**
   - Put `F = 1 − min(1, W_{k−1}/ε_k)`. Its rank exceeds that of `x_k` by at least
     `1 − t − 3ε/4` at every trace.
   - Strict comparison and Rørdam's lemma give `c_k` with `c_k c_k* = (x_k − ε'_k)_+` and
     `c_k* c_k ∈ her(F)`.
   - `c_k* c_k` is orthogonal to `(W_{k−1} − ε_k)_+`. Put
     `W_k = (W_{k−1} − ε_k)_+ + c_k* c_k`.
6. **Result.** The ranks of the orthogonal pieces add, so `|d_τ(W_L) − t| ≤ 3ε/4` at
   every trace.
7. **Division.** Strict comparison gives `n[W_L] ≤ [1] ≤ (n+1)[W_L]` for every `n`.
   Item 3 ⟹ item 1 of the equivalences divides the unit. ∎
