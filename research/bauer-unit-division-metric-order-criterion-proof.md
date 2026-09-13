---
rg: 2
id: bauer-unit-division-metric-order-criterion-proof
kind: route
title: Charge each local division only its defect by a refined spectral bound, then cover below the Lebesgue number of local divisions
target: bauer-unit-division-metric-order-criterion
requires:
  - strict-comparison-unit-divisibility-equivalences
artifacts:
  - research/artifacts/ex-tw-c-space-unit-division-2026-09-13.md
  - research/artifacts/ex-tw-c-space-unit-division-part2-2026-09-13.md
  - research/artifacts/ex-tw-c-space-unit-division-part4-2026-09-13.md
---

Sections 8–9 of the part 4 artifact, over Lemmas 1 and 3 of part 1 and Section 3 of
part 2.

1. **Lemma 8.1.** For a positive contraction `b` and `σ ≤ 1/2`,
   `λ(b) ≤ ∫_{(0,σ]} x dμ + μ((σ,1])`, and `x ≤ 2(x − x²)` on `(0,σ]`. So
   `μ((σ,1]) ≥ λ(b) − 2λ(b − b²)`.
2. **Linear weights (⟸).** Take a family with `Σ_{i∋λ}(1/N_i + δ_i) ≤ ε_0²/64`, and a
   single cutoff `s = ε_0/8`.
   - **Upper bounds.** Active members add at most `t h_i(1+2s) + 2d_i/s` plus
     `η`-terms; inactive members add at most `8η/s`.
   - **Lower bounds.** Lemma 8.1 gives at least `t h_i − δ_i − 2d_i` minus `η`-terms.
   - **Sums.** The rank sums lie in `[t − ε_0/4, t + 5ε_0/8]`. Every move keeps margin
     at least `1/8`.
   - **Conclusion.** Strict comparison, Rørdam's lemma and exact orthogonality proceed as
     in Section 3 of part 2. Item 3 ⟹ item 1 of
     `strict-comparison-unit-divisibility-equivalences` divides the unit.
3. **(⟹).** `K` alone, at large `N` and small `δ`.
4. **Metric criterion.**
   - Members of a finite cover of mesh `< ℓ_A(ω)` lie inside division sets of weight
     `≤ ω`, so they are division sets.
   - Their pointwise weight sum is at most `ω · ord_K(ℓ_A(ω))`, and step 2 applies.
5. **Hilbert cube bound.** Pull back covers of `[0,1]^D` of mesh `< r/2` and order `D + 1`,
   with `D = ⌈log_2(4/r)⌉`. The tail coordinates add at most `2^{−D} ≤ r/4` to diameters. ∎
