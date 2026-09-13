---
rg: 2
id: bauer-unit-division-defect-uniform-criterion-proof
kind: route
title: Charge each staircase its per-piece defect and a profile-weighted defect, then rerun the moves of Proposition 8.2
target: bauer-unit-division-defect-uniform-criterion
requires:
  - strict-comparison-unit-divisibility-equivalences
artifacts:
  - research/artifacts/ex-tw-c-space-unit-division-2026-09-13.md
  - research/artifacts/ex-tw-c-space-unit-division-part2-2026-09-13.md
  - research/artifacts/ex-tw-c-space-unit-division-part4-2026-09-13.md
  - research/artifacts/ex2-tw-hilbert-cube-defect-uniform-division-2026-09-13.md
---

Sections H.1–H.3 of `research/artifacts/ex2-tw-hilbert-cube-defect-uniform-division-2026-09-13.md`,
over Lemmas 1 and 3 and (F1)–(F5) of part 1, Section 3 of part 2 and Lemma 8.1 of part 4.

1. **Lemma H.1.** Let `f(s) = s − s²`. By order zero functional calculus, `f(φ)` is order zero with
   `f(φ)(e_jj) = e_j − e_j²`. So (F4) gives `λ(e_j − e_j²) = λ(φ(1) − φ(1)²)/N ≤ δ/N` on `supp h`.
   - At most `Nth(λ) + 1` coefficients are nonzero, and at most one lies strictly between 0 and 1.
   - Hence `λ(B − B²) ≤ 1/(4N) + δ/N + t h(λ)δ`.
2. **(⟸).** Fix `n`, and take `t, γ` as in Section 3, `ε_0 = γ/2`, `s = ε_0/8` and `κ = ε_0²/384`.
   Take a family with `Σ_{i∋λ} 1/N_i ≤ κ` and `δ_i ≤ κ`.
   - **Upper bounds.** Active members contribute at most `(t h_i + η)(1+2s) + 2(D_i + 3η)/s`, and
     inactive members at most `8η/s`.
   - **Lower bounds.** Lemma 8.1 gives `t h_i(1 − δ_i) − η − 2(D_i + 3η)` for active members.
   - **Sums.** `Σ_active D_i ≤ 2κ + tκ`, so the rank sums lie in `[t − ε_0/8, t + ε_0/2]`.
   - **Moves.** Every move keeps margin `> 1/8`. Strict comparison, Rørdam's lemma and exact
     orthogonality apply as in Step 5 of Section 3.
   - **Division.** Step 7 gives `n[W] ≤ [1] ≤ (n+1)[W]` for every `n`. Item 3 ⟹ item 1 of
     `strict-comparison-unit-divisibility-equivalences` divides the unit.
3. **(⟹).** A global order zero `φ: M_N → A` with `N ≥ 1/κ` and defect `< κ` is a one-member family.
4. **Metric form.** A cover of mesh below `ℓ_A(N, δ)` and minimal order gives `Σ 1/N_i ≤ ord/N`.
   Conversely, a divisible unit makes `K` a division set, so `ℓ_A = ∞`.
5. **Hilbert cube.** Negate the metric form at `δ = κ_0`, and use `ord_Q(r) ≤ log_2(4/r) + 2`
   (part 4, Section 9).
