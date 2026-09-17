---
rg: 2
id: fpbs-fixed-pseudocost-from-relative-sandwich-bound
kind: route
title: Apply the relative Bernoulli bound in each finitely generated subgroup, take inf over subgroups and sup over finite sets
target: fpbs-countable-groups-have-fixed-pseudocost
requires:
  - fpbs-relative-sandwich-cost-bernoulli-lower-bound
  - fpbs-pseudocost-localizes-to-fg-sandwich-costs
  - tucker-drob-sandwich-sets-open-at-free-actions
  - abert-weiss-free-actions-weakly-contain-bernoulli
artifacts:
  - research/artifacts/fpbs-sandwich-cost-quantifier-shift-2026-09-17.md
---

Direct proof (artifact Theorem 3.1). Let `Γ` be countably infinite, `a` a free
p.m.p. action of `Γ`, and `F ⊆ Γ` finite. Write `p_F = p^Γ_F`.

1. **Each finitely generated subgroup.** Let `Δ ≤ Γ` be finitely generated
   with `F ⊆ Δ`. The restriction `a|Δ` is free. Then:
   - `p_F(s_Γ) ≤ p^Δ_F(s_Γ|Δ)`, by item 1 of
     `fpbs-pseudocost-localizes-to-fg-sandwich-costs` (a sandwich relation
     over `Δ` is one over `Γ`);
   - `p^Δ_F(s_Γ|Δ) = p^Δ_F(s_Δ)`, by item 3 of the same node;
   - `p^Δ_F(s_Δ) ≤ p^Δ_F(a|Δ)`, by
     `fpbs-relative-sandwich-cost-bernoulli-lower-bound` applied to `Δ`, `F`
     and `a|Δ`.
2. **Infimum over subgroups.** Item 1 of the localization node gives
   `p_F(a) = inf_Δ p^Δ_F(a|Δ)`. So `p_F(s_Γ) ≤ p_F(a)`.
3. **Supremum over finite sets.** Item 2 of the localization node gives
   `PC(s_Γ) = sup_F p_F(s_Γ) ≤ sup_F p_F(a) = PC(a)`.
4. **Reverse inequality.**
   - `s_Γ` is free (item 4 of the localization node).
   - `abert-weiss-free-actions-weakly-contain-bernoulli` gives `s_Γ ≼ a`.
   - Item (4) of `tucker-drob-sandwich-sets-open-at-free-actions` gives
     `PC(a) ≤ PC(s_Γ)`.

So `PC(a) = PC(s_Γ)` for every free `a`.
