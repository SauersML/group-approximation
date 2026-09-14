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
