---
rg: 2
id: sylvester-rank-functions-descend-to-quotients-and-compressions
kind: claim
title: A Sylvester rank function induces Sylvester rank functions on ideal quotients and on commuting compressions
distinct_from:
  corner-defect-killing-rank-functions-are-augmentation: that pulls a rank function back along a corner map and uses the augmentation criterion; this builds new rank functions from a two-sided ideal or from a commuting element, with no idempotent and no regular envelope.
artifacts:
  - research/artifacts/sylvester-class-a-defect-chain-2026-09-12.md
---

**ESTABLISHED** (lane `w5-regular-rankfn`; verified PASS by `w4-vf-gate`, Section 26 of
`research/artifacts/gk-vf-gate-verification-2026-09-12.md`, fbcf9d2005) by
`sylvester-quotients-and-compressions-proof`.

Let `rho` be a Sylvester matrix rank function on a unital ring `S`. For a `k x 1` column `X` and a matrix `A` with
`m` rows write `X A := (X (x) I_m) A`.

1. **Ideal quotients.** Let `J` be a two-sided ideal generated as a left ideal by `x_1, ..., x_k`,
   `X = (x_1, ..., x_k)^T`, with `rho(X) > 0`. Then `rho_J(A) := rho(X A) / rho(X)` is a Sylvester matrix rank
   function on `S`, independent of the generators. If `J = J^2`, then `rho_J(X Z) = rho_J(Z)` for every `Z`.
2. **Commuting compressions.** Let `C` be a unital subring and `d` a `k x k` matrix over `S` commuting with every
   `c I_k`, `c` in `C`, with `rho(d) > 0`. Then `rho_d(A) := rho((A (x) I_k)(I_n (x) d)) / rho(d)` is a Sylvester
   matrix rank function on `C`.
3. **Inequalities used with them.** Every Sylvester rank function satisfies the Sylvester inequality
   `rho(A) + rho(B) <= n + rho(AB)` (so square-zero elements have `rho <= 1/2`), the Frobenius inequality
   `rho(AB) + rho(BC) <= rho(B) + rho(ABC)`, and stacking `rho([A; B]) <= rho(A) + rho(B)`.

In a faithful regular rank ring, `rho_J` is the model on the quotient by the `J`-annihilated summand and `rho_d` is
the corner model on the image of `d`. So these replace the idempotent corners of the defect chain wherever the
corner is a quotient by an ideal or an image of a commuting element.

## Attempts

Established, not open. Proof in artifact Section 1.
