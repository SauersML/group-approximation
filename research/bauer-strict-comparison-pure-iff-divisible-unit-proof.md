---
rg: 2
id: bauer-strict-comparison-pure-iff-divisible-unit-proof
kind: route
title: A divided unit gives rank density on Bauer simplices, rank density with strict comparison gives purity, and purity divides the compact unit
target: bauer-strict-comparison-pure-iff-divisible-unit
requires:
  - bauer-tracially-divisible-unit-gives-bounded-rank-density
  - rank-density-and-strict-comparison-give-purity
  - strict-comparison-unit-divisibility-equivalences
artifacts:
  - research/artifacts/ex-toms-winter-unit-divisibility-equivalences-2026-09-12.md
  - research/artifacts/ex-toms-winter-bauer-divisible-unit-2026-09-12.md
---

Let `A` be unital, simple, separable, exact and non-elementary, with Bauer `T(A)`
and strict comparison. Traces on the simple unital `A` are faithful, so `A` is
stably finite.

1. **(e) ⟹ (c).** `bauer-tracially-divisible-unit-gives-bounded-rank-density`.
2. **(c) ⟹ (b).**
   - Given continuous strictly positive affine `f` and `η > 0`, take `k ≥ sup f`.
     RD_b gives a positive contraction `q ∈ M_k(A)` with `|τ(q) − f(τ)| < η/3` and
     `τ(q − q²) < η/3`.
   - Integrating `1_{(1/2,1]}(t) ≤ t + 2t(1−t)` and `t ≤ 1_{(1/2,1]}(t) + 2t(1−t)`
     against spectral measures gives `|d_τ((q − 1/2)_+) − τ(q)| ≤ 2τ(q − q²)`.
     These are the estimates of Section 1, Step 2 of
     `research/artifacts/toms-winter-tracial-ultrapower-comparison-2026-09-12.md`.
   - So `|d_τ((q − 1/2)_+) − f(τ)| < η` for every `τ`.
3. **(b) ⟹ (a).** `rank-density-and-strict-comparison-give-purity` (unital simple
   separable exact stably finite non-elementary, strict comparison, rank density).
4. **(a) ⟹ (d).**
   - Almost divisibility of `Cu(A)` at `x = x' = [1_A]`, which is compact, gives
     `y ∈ Cu(A)` with `n y ≤ [1]` and `[1] ≤ (n+1) y`.
   - Write `y = sup_m y_m` with `y_m ∈ W(A)` increasing. Since `[1] ≪ [1]`, some
     `y_m` has `[1] ≤ (n+1) y_m`, and `n y_m ≤ n y ≤ [1]`.
5. **(d) ⟺ (e) ⟺ (f).** `strict-comparison-unit-divisibility-equivalences`: items 3,
   1 and 5 there.
6. **Counterexample clauses.**
   - Negate (d).
   - Unique-trace subalgebras give (e) by Lemma 3.1 of
     `research/artifacts/ex-toms-winter-bauer-divisible-unit-part2-2026-09-12.md`.
   - Unital `Z_{n,n+1}` gives (d) at `n`, by Rørdam–Winter (iv) ⟹ (i), their
     reference [15, Lemma 4.2]. That step was not re-read.
