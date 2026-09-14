---
rg: 2
id: subshift-elementary-root-continuous-characters-are-trivial
kind: claim
title: A character of EL_3(LC(X,F_2) ⋊ Z) that tends to 1 on root elements of small support is trivial
distinct_from:
  subshift-elementary-groups-are-character-rigid: that is the full classification (every extreme character is 1 or regular); this proves the continuous half only, which rules out measure-type characters and leaves discontinuous ones open.
  ah-groups-fail-regular-fd-character-rigidity: that shows acylindrically hyperbolic groups never have regular-or-finite-dimensional character rigidity; this constrains the characters of one explicit simple Kazhdan LEF group.
artifacts:
  - research/artifacts/sk-characters-root-continuity-2026-09-13.md
---

**ESTABLISHED (unreviewed).**
- `X` is an infinite minimal subshift, `R = LC(X,F_2) ⋊_T Z` and `G = EL_3(R)`.
- For clopen `P ⊆ X` put `‖P‖ = sup_μ μ(P)`, the supremum over `T`-invariant probability measures.

Let `χ` be a character of `G`: positive definite, conjugation invariant, `χ(e) = 1`. If `χ(e_12(e_P)) → 1` as `‖P‖ → 0`, then `χ ≡ 1`.

Consequences:
- **Discontinuity.** Every nontrivial character, the regular character included, is bounded away from 1 at some root elements `e_12(e_{P_n})` with `‖P_n‖ → 0`.
- **No measure-type characters.** If `χ(e_12(e_P)) = F(μ(P))` for one invariant `μ` and some `F` continuous at 0 with `F(0) = 1`, then `χ ≡ 1`. So `G` has no analogue of the Dudko–Medynets characters `γ ↦ ∏ μ_i(Fix γ)` of the derived topological full group (arXiv:2602.16885, Thm 1.1).
- **Invariant random subgroups.** An IRS `ν` with `ν{H : e_12(e_P) ∈ H} → 1` as `‖P‖ → 0` equals `δ_G`.

The same holds for `EL_n(LC(X,F_q) ⋊ Z)/Z` with `n ≥ 3`. Proof: route `subshift-elementary-root-continuous-characters-proof`.
