---
rg: 2
id: fpbs-mal-floor-iff-deep-promotion-floor-proof
kind: route
title: Telescope cheap one-step promotions with the stage shift, truncate labels to a finite stage, and transport each stage triple to F_2
target: fpbs-mal-floor-iff-deep-promotion-floor
requires:
  - fpbs-shifted-stage-relative-cost-zero-or-infinite
artifacts:
  - research/artifacts/fpbs-deep-promotion-reduction-2026-09-18.md
---

The full proof is §1–§2 of `fpbs-deep-promotion-reduction-2026-09-18.md`.

1. **Promotion from relC.** A graphing admissible for `relC(E; R_1)` joins
   `R_1` to `E ⊇ R_2`. So `q_infinity <= relC(E; R_1)`.
2. **Telescoping.** Suppose `q_infinity = 0`. Choose promotions `Psi^(k)`
   of mass `< eps 2^{-k}`, and conjugate them by `T^{k-1}`, where `T`
   implements the stage shift of
   `fpbs-shifted-stage-relative-cost-zero-or-infinite`. The conjugate promotes
   `R_k` to `R_{k+1}`. By induction the union promotes `R_1` to every
   `R_{k+1}`, hence to `E`, at mass `< eps`. So `relC(E; R_1) = 0`.
3. **Truncation.** Given a promotion `Psi` inside `E`, split it into label
   pieces and keep those with label in `H_m`. The relations generated
   increase to one containing `(x, b_2 x)` almost everywhere. So the set
   where `(x, b_2 x)` is missed has measure `< delta` for large `m`. Adding
   `b_2` there gives a promotion inside `R_m`, of cost at most
   `C(Psi) + delta`. So `q_infinity = lim q_m`.
4. **Transport.** `psi_m : H_m -> F(a, b)`, with `a -> a` and `b_m -> b`,
   sends `H_{m-j}` to `phi^j(L)`, because `psi_m(b_{m-j}) = phi^j(b)`, by
   induction. `beta|H_m` is a Bernoulli shift of `H_m`: fix representatives
   of the right cosets of `H_m`, and note that the base
   `[0,1]^{H_m \ Gamma}` is standard and non-atomic. So `q_{j+2} = Q_j`.
5. **Conclusion.** Combine steps 1–4. `Q_j` is nonincreasing because `q_m` is.
