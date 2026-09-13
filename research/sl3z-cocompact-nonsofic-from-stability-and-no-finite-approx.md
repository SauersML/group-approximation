---
rg: 2
id: sl3z-cocompact-nonsofic-from-stability-and-no-finite-approx
kind: route
title: Stability in finite actions turns a sofic model of SL3(Z) on SL3(R)/Λ into weak containment in finite actions, which the open exclusion forbids
target: sl3z-on-cocompact-lattice-quotient-is-not-sofic
requires:
  - sl3z-cocompact-quotient-not-weakly-contained-in-finite-actions
  - sl3z-is-stable-in-finite-actions
  - uniquely-ergodic-action-sofic-iff-topological-microstates
---

Conditional route. Let `Λ` be as in `sl3z-cocompact-quotient-not-weakly-contained-in-finite-actions`,
`Γ = SL_3(Z)`, `X = SL_3(R)/Λ`, and suppose `Γ ↷ X` is sofic.

1. **Microstates.** By part 1 of `uniquely-ergodic-action-sofic-iff-topological-microstates` there are
   `(F_k, ε_k)`-microstates `(V_k, σ_k, y_k)` with `F_k ↑ Γ` and `ε_k → 0`.
2. **Residual amplification.** Replace `V_k` by `V_k × Q_k` for finite quotients `Q_k` of `Γ` that are
   injective on `F_k`. Act diagonally and pull `y_k` back along the first coordinate. Defects and
   covariance errors do not change, and `σ_k × q_k` is a sofic approximation (Lemma 3.2 of Alekseev--Thom,
   as in `stable-finite-actions-coset-nonsofic-proof`).
3. **Factor map.** Let `β` be the p.m.p. action on the Loeb ultraproduct `Z` of step 2. `X` is compact, so
   the standard part of `lim_U y_k` is a Loeb-measurable `π : Z → X`. By the microstate bounds it is
   `Γ`-equivariant almost everywhere, and by Step A of the criterion's proof it pushes the Loeb
   measure to Haar measure. So `Γ ↷ X` is a factor of `β`.
4. **Weak containment.** By `sl3z-is-stable-in-finite-actions`, `β` is weakly contained in finite actions,
   hence so is its factor `Γ ↷ X`. This contradicts `sl3z-cocompact-quotient-not-weakly-contained-in-finite-actions`
   in its equivalent form 1. ∎
