---
rg: 2
id: fpbs-locally-free-finite-cost-from-relative-free-pairs
kind: route
title: Build a rank-at-most-c* free chain and sum rank-difference relative costs along it
target: fpbs-locally-free-free-actions-have-finite-cost
requires:
  - fpbs-relative-fixed-price-free-pairs
  - fpbs-relative-stage-costs-bound-cost-by-stage-liminf
artifacts:
  - research/artifacts/fpbs-relative-fixed-price-decomposition-2026-09-17.md
---

Artifact §3.1, Proposition 2. Let `Γ` be countably infinite and locally free,
with `c*(Γ) < ∞`, and let `a` be a free action.

1. **Chain.** Let `F_n` be finite sets increasing to `Γ`, with `F_1`
   containing a nontrivial element. Given a finite generating set `S_{n-1}`
   of `Γ_{n-1}`, choose a finitely generated `Γ_n ⊇ F_n ∪ S_{n-1}` of minimal
   rank.
   - That rank is `c_{F_n ∪ S_{n-1}} ≤ c*`, with `c_F` and `c*` as in
     `locally-free-groups-first-l2-betti-equals-c-star-minus-one`.
   - The `Γ_n` are nontrivial free groups increasing to `Γ`.
2. **Stage costs.** `a|Γ_n` is free, so Gaboriau's lecture notes Cor 2.25
   ("The following groups are strongly treeable and have fixed price:
   C∗(Fn) = C∗(Fn) = n for the free group of rank n.") gives
   `C(E_{a|Γ_n}) = rk Γ_n ≤ c*`.
3. **Relative costs.** `fpbs-relative-fixed-price-free-pairs`, applied to
   `Γ_n ≤ Γ_m` and the free action `a|Γ_m`, gives
   `relC ≤ (rk Γ_m − rk Γ_n)^+`.
4. **Conclusion.** `fpbs-relative-stage-costs-bound-cost-by-stage-liminf`
   gives `C(a) ≤ liminf rk Γ_n ≤ c* < ∞`, which is the target. ∎

Combined with the ESTABLISHED
`fpbs-locally-free-free-action-costs-are-c-star-or-infinite`, every free action
has cost exactly `c*`.
