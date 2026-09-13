---
rg: 2
id: degree-one-bernoulli-expansion-excludes-weak-lifts-proof
kind: route
title: Expansion turns the flipped approximate trivialization into an exact cocycle, and Popa plus the Bernoulli spectral gap forces a constant cochain
target: degree-one-bernoulli-expansion-excludes-weak-lifts
requires:
  - popa-bernoulli-cocycle-superrigidity
  - bernoulli-maximizes-extension-class-norm
artifacts:
  - research/artifacts/weakly-bernoulli-lifts-degree-one-reduction-2026-09-13.md
---

Section 14 of the artifact (Theorem R1), with explicit error chaining.
1. **Two copies.** `|delta b - alpha_0| <= eps`, so `d = b∘p_1 - b∘p_2` on `X^2` has `|delta d| <= 2 eps`.
2. **Expansion.** There is an exact `z` with `|d - z| <= rho(2 eps) = eps_1`.
3. **Popa.** `z = delta f + chi`.
4. **Three copies.** `F = f_12 + f_23 - f_13` has `|F∘s^-1 - F + chi(s)| <= 3 eps_1`.
5. **Spectral gap.**
   - `Gamma` is non-amenable, so the Koopman representation on `L^2_0` of a Bernoulli shift, twisted by any character,
     has no almost invariant vectors, with a uniform constant `K`.
   - Applied to `psi∘F` for characters `psi` of `A`, this forces `chi = 0` once `sqrt(eps_1)` is below a threshold,
     and `F = c` off `C eps_1`.
6. **Fubini.** `f ≈ g∘p_1 - g∘p_2 + c`.
7. **Near constant.** `h_s = b_s - (g∘s^-1 - g)` agrees across independent copies off `eps_3`, so it is `eps_3`-close
   to a constant `a_s`.
8. **Splitting.** `delta a = alpha_0` off `eps + ell eps_3` at every relator. Both sides are constants, so for small
   `eps` they are equal, and `alpha = 0`.
9. **Weak lifts.** The Bernoulli norm of a nonzero class is at least the resulting `eps_0`. Item 4 of
   `bernoulli-maximizes-extension-class-norm` then excludes weakly Bernoulli lifts.
