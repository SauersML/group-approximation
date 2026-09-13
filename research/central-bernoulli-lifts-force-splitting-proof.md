---
rg: 2
id: central-bernoulli-lifts-force-splitting-proof
kind: route
title: Flip the lifting cochain across independent copies, apply Popa to the difference cocycle, and separate variables on three copies
target: central-bernoulli-lifts-force-splitting
requires:
  - popa-bernoulli-cocycle-superrigidity
  - bernoulli-maximizes-extension-class-norm
artifacts:
  - research/artifacts/weakly-bernoulli-lifts-degree-one-reduction-2026-09-13.md
---

Section 13 of the artifact (Theorem R0).
1. **The lift as a cochain.** By item 1 of `bernoulli-maximizes-extension-class-norm`, the lift gives
   `b in C^1([0,1]^Gamma, A)` with `delta b = alpha_0`.
2. **Two copies.** `d = b∘p_1 - b∘p_2` on the Bernoulli shift `X^2` (base `[0,1]^2`) has `delta d = 0`.
3. **Popa.** `d = delta f + chi` with `chi in Hom(Gamma, A)`.
4. **Three copies.** On `X^3`, `F = f_12 + f_23 - f_13` satisfies `delta F + chi = 0`, because
   `d_12 + d_23 - d_13 = 0`.
5. **Kill `chi`.** `F` is invariant under `ker chi`, which acts ergodically, so `F` is constant, `chi = 0`, and `F = c`.
6. **Separate variables.** For a.e. `y`, `f(x,x') = g(x) - g(x') + c` with `g = f(., y)`.
7. **Constant cochain.** Then `(b - delta g)(x) = (b - delta g)(x')` a.e., so `b - delta g = a` is constant.
8. **Splitting.** `alpha_0 = delta a`.
