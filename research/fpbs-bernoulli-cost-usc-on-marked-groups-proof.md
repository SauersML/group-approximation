---
rg: 2
id: fpbs-bernoulli-cost-usc-on-marked-groups-proof
kind: route
title: Truncate a near-optimal graphing to cylinder data with an exact repair, whose cost is read off a finite ball, and test lower semicontinuity on central amalgams converging to free groups
target: fpbs-bernoulli-cost-usc-on-marked-groups
requires:
  - fpbs-bernoulli-maximal-cost
  - fpbs-infinite-centralizer-forces-price-one
  - fpbs-amen2-betti-cost-input
  - decidable-groups-have-right-computable-l2-betti-numbers
artifacts:
  - research/artifacts/fpbs-bernoulli-cost-marked-usc-2026-09-20.md
---

The full proof is in the artifact. §1 gives item 1, §2 item 2 and §3 item 3.

1. **Upper semicontinuity (§1).**
   - Take a graphing of cost `< C*(Γ) + ε`.
   - Keep finitely many pieces, and replace their domains by cylinder sets.
   - Add a repair edge `s_i|D_i`, where `D_i` is exactly the set on which `s_i x` is
     not reached from `x` within `L` steps. The result generates `E_{s_Γ}` exactly, at
     cost `< C*(Γ) + 3ε`.
   - Freeness turns "reached" into the condition `β_p = s_i` on path words.
   - Every set involved is a Boolean combination of coordinate atoms at boundedly long
     words. Its product measure depends only on which of those words are equal.
   - So the same datum, read in any `Γ_n` with the same `R`-ball, gives an exactly
     generating graphing of `E_{s_{Γ_n}}` of the same cost.
   - `C* = C(s_Γ)` is the maximal free-action cost by `fpbs-bernoulli-maximal-cost`.
2. **Failure of lower semicontinuity (§2).**
   - `⟨a_1, …, a_k | [a_i, a_1^n]⟩ = (Z × F_{k-1}) *_{Z} Z`.
   - Freely reduced words of length `< n` are reduced alternating products, hence
     nontrivial, so the groups converge to `F_k`.
   - `a_1^n` is central of infinite order, so
     `fpbs-infinite-centralizer-forces-price-one` gives fixed price one.
   - `C*(F_k) = k`, by `fpbs-amen2-betti-cost-input` with `β_1^(2)(F_k) = k - 1`.
3. **Arithmetic form (§3).**
   - The costs of all finite data are computable rationals, and their infimum is `C*`.
   - Right-computability of `β_1^(2)` is
     `decidable-groups-have-right-computable-l2-betti-numbers`.

The class kill (§4) uses only items 1 and 2 and Pichot's upper semicontinuity of
`β_1^(2)`. Source: M. Pichot, *Semi-continuity of the first l²-Betti number on the
space of finitely generated groups*, Comment. Math. Helv. 81 (2006), 643–652. Pichot
is quoted only for context. Items 1–3 do not depend on it.
