---
rg: 2
id: transport-identity-gives-reciprocal-memory-entropy-bound-proof
kind: route
title: Recover the input site from the decoder window and use subadditivity with shift invariance
target: transport-identity-gives-reciprocal-memory-entropy-bound
requires: []
artifacts:
  - research/artifacts/three-point-decoder-transport-obstruction-2026-09-12.md
---

Artifact Section 1, Proposition 1. The direct proof is w3-vf-positive's (2026-09-12).

Let `y = kappa(x)` with `x` uniform on `A^G`, and let `sigma` be a left inverse with memory `N`.
1. `x(e) = nu(y|_N)` is a function of `y|_N`, so `log |A| = H(x(e)) <= H(y|_N)`.
2. Subadditivity gives `H(y|_N) <= sum_(n in N) H(y(n))`.
3. `kappa` is equivariant and the uniform product measure is shift invariant, so each `y(n)` has the law of `y(e)`.
4. Hence `log |A| <= |N| H(y(e))`. QED

**Second derivation.** Bound each term `E_U I(x(n^-1); y(e) | Z_n, U)` of
`injective-ca-random-order-transport-identity` by `H(y(e))`, which does not depend on `U`, and sum the `|N|` terms. This
shows the identity with per-term entropy bounds gives nothing beyond subadditivity. The claim does not depend on it.

**Verification.** `w4-vf-positive-b` passed this route in Section 5.2 of
`research/artifacts/gk-vf-positive-b-verification-2026-09-12.md`.
- **The bound is not the best elementary one.** It is the `F = {e}` case of the counting bound
  `log |A| sup_F |F|/|FN|`, which already does better on some nonamenable decoder memories.
- **Example:** with `N = {e, s, t}` and `s, t` generating a free semigroup, the counting bound gives the constant `1/2`.
