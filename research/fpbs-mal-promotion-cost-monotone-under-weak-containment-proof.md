---
rg: 2
id: fpbs-mal-promotion-cost-monotone-under-weak-containment-proof
kind: route
title: Transfer the finitely many words realising each extra generator with one conjugator, fix up the missed set, and apply Abert-Weiss at each depth
target: fpbs-mal-promotion-cost-monotone-under-weak-containment
requires:
  - fpbs-finite-cost-transfers-up-weak-containment
  - abert-weiss-free-actions-weakly-contain-bernoulli
  - fpbs-mal-floor-iff-deep-promotion-floor
artifacts:
  - research/artifacts/fpbs-promotion-cost-weak-containment-2026-09-18.md
---

The full proof is §1–§3 of `fpbs-promotion-cost-weak-containment-2026-09-18.md`.

1. **Words.** Take `Φ` promoting `E_{a|H'}` to `E_{a|H}` at cost within `ε`
   of the infimum. For each `s ∈ F`, Lemma 2 of the transfer artifact
   (`fpbs-finite-cost-transfers-up-weak-containment`, with `K = H'`) gives
   finitely many words of value `s` whose domains cover `1 − δ`. It uses
   freeness of `a`, and labels may lie anywhere in `Γ`.
2. **Transfer.** Lemma 1 of the transfer artifact (Burton–Kechris
   conjugacy-closure form of `a ≼ b`) copies the finitely many pieces used
   into `b` with the same masses. The copied domains then cover `1 − 2δ`.
3. **Fix-up.** Add `(Y ∖ U^b_s, s)` for each `s ∈ F`, at mass `≤ 2δ` each.
   The graphs of all `s^b` now lie in `E_{b|H'} ∨ Ψ`, so `Ψ` promotes to
   `E_{b|H}`. Letting `ε, δ → 0` proves Theorem M.
4. **Depths.** By Abért–Weiss Theorem 1, `ρ ≼ c` for every free `c`. Apply
   Theorem M with `F = {φ^j(b)}`, `H' = L_{j+1}` and `H = L_j`. The cap
   `Q_j(c) ≤ Q_0(ρ)` comes from the free action `c ∘ φ^j` and Corollary 5 of
   the transfer node.
5. **Equivalence.** `fpbs-mal-floor-iff-deep-promotion-floor` gives
   floor iff `inf_j Q_j(ρ) > 0`. Combine it with step 4.
6. **Profinite.** Approximate the finitely many pieces by level-n cylinders,
   whose translates are level-n cylinders. Reachability over a cylinder
   family depends only on the level-n image of the point, by freeness.
