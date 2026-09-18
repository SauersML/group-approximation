---
rg: 2
id: fpbs-cost-is-limit-of-cayley-subgraphing-costs-proof
kind: route
title: Split graphing pieces into translations, truncate to finitely many labels, and back up the unconnected generator edges on a vanishing set
target: fpbs-cost-is-limit-of-cayley-subgraphing-costs
requires:
  - fpbs-bernoulli-morse-collapse-criterion
  - fpbs-morse-mass-bounded-by-relator-boundary-rank
  - fpbs-graphing-cost-betti-cycle-dimension-identity
artifacts:
  - research/artifacts/fpbs/docs/adapted-generating-sets-make-morse-deficit-lossless.md
---

Written derivation, Sections 1–3 of the artifact.

1. **Monotonicity.** Subgraphings of `Phi_S` are subgraphings of `Phi_(S')` for `S ⊆ S'`, and are graphings. So
   `C(a) <= C_sub^a(S') <= C_sub^a(S)`, and `lim_R C_sub^a(B_R) = inf_S C_sub^a(S) >= C(a)`.
2. **Translations.** By freeness each piece `phi_i` of a generating graphing `Psi` splits into Borel pieces
   `x -> gamma.x`. The resulting edge set `E_Psi ⊆ X x (Gamma \ {1})` generates and costs at most `c(Psi)`.
3. **Truncation.** Keep the labels `gamma_1, ..., gamma_N`; the generated relations `R_N` increase to `R_a`.
4. **Backup.** Add the `S_0`-edges `(x, s)` with `(x, s.x)` not in `R_N`. Their measure tends to `0` by dominated
   convergence, and the union generates because `S_0` generates `Gamma`. This proves (E).
5. **(F).** Theorem B(ii) of `fpbs-bernoulli-morse-collapse-criterion` at `S = B_R` gives
   `lim_L m_(B_R)(P_L) = C_sub(B_R) - 1 - beta_1`; take `R -> infinity` with (E). The `A`-form follows from
   `m = gap + A` with `gap(P_L) -> 0`, from `fpbs-morse-mass-bounded-by-relator-boundary-rank`.
6. **(G).** `lim_L m_S(P_L) = (C_sub(S) - C(b)) + (C(b) - 1 - beta_1)`, a sum of two nonnegative terms by step 1 and
   `fpbs-graphing-cost-betti-cycle-dimension-identity`. Upward closure: `C(b) <= C_sub(S') <= C_sub(S) = C(b)`.

This is dependency bookkeeping over a written deduction, not a formal verification.
