---
rg: 2
id: fpbs-finite-normal-quotient-lifts-price-one-proof
kind: route
title: Let the quotient act on a Borel fundamental domain of the finite kernel and apply the complete-section induction formula
target: fpbs-finite-normal-quotient-lifts-price-one
requires:
  - fpbs-normalized-cost-induction-input
artifacts:
  - research/artifacts/fpbs-infinite-centralizer-price-one-2026-09-16.md
---

Complete written proof. It is Lemma A in Section 2 of the linked artifact.

Let `Gamma` act freely on `(X, mu)`, preserving `mu`, and put `Q = Gamma/F`.

1. **Fundamental domain.**
   - Fix a Borel injection `tau : X -> R` and let
     `D = {x : tau(x) < tau(f x) for all f in F \ {e}}`.
   - `F` acts freely, so `D` meets each `F`-orbit in exactly one point.
   - So `X` is the disjoint union of the `f D`, and `mu(D) = 1/|F|`.
   - Let `r : X -> D` pick the point of `D` in `F x`. It is Borel.
2. **Action.**
   - Put `(gamma F) . x = r(gamma x)` for `x in D`.
   - This is well defined and an action, because `F` is normal:
     `gamma f x in F gamma x`.
3. **Measure preserving.**
   - For `q = gamma F`, the Borel sets `D_f = {x in D : f gamma x in D}`
     partition `D`, and `q . x = f gamma x` on `D_f`.
   - `q .` is injective on `D`: `r(gamma x) = r(gamma x')` forces
     `x' in F x`, so `x = x'`.
   - So `q .` is a measure-preserving Borel bijection of `D`.
4. **Free.** `q . x = x` gives `f gamma x = x` for some `f in F`. Freeness of
   `Gamma` gives `gamma in F`.
5. **Orbits.** If `x, y in D` and `y = gamma x`, then `y = r(gamma x)`. So the
   orbit relation of `Q` on `D` is `R_Gamma|D`.
6. **Cost.** `D` is a complete section of `R_Gamma`.
   `fpbs-normalized-cost-induction-input` with `mu(D) = 1/|F|` gives
   `C(R_Gamma) - 1 = (C(R_Q on D) - 1)/|F|`.
7. **Conclusion.** If `Q` has fixed price one, the right side is zero, so
   `C(R_Gamma) = 1` for every free action.

This is dependency bookkeeping for a written proof, not a formal verification.
