---
rg: 2
id: fpbs-shifted-stage-relative-cost-zero-or-infinite-proof
kind: route
title: Transport stage pairs by the shift automorphism, then truncate a finite-cost graphing by labels
target: fpbs-shifted-stage-relative-cost-zero-or-infinite
requires:
  - fpbs-locally-free-free-action-costs-are-c-star-or-infinite
artifacts:
  - research/artifacts/fpbs-shifted-stage-relative-cost-zero-or-infinite-2026-09-17.md
---

The complete proof is §1–§2 of the artifact. It is self-contained apart from
two imports:
- the value `2` (instead of "finite") for `Gamma_mal` uses
  [[fpbs-locally-free-free-action-costs-are-c-star-or-infinite]] with `c* = 2`;
- the stage costs `C(R_n) = 2` use Gaboriau's lecture notes, Corollary 2.25,
  verbatim: "The following groups are strongly treeable and have fixed price:
  C∗(Fn) = C∗(Fn) = n for the free group of rank n."

1. **Transport.** `T(R_n) = R_{n+1}` and `T(E) = E`, so `T` is an
   isomorphism of pairs. Relative cost is an isomorphism invariant.
2. **Truncation.** Split a finite-cost graphing of `E` into pieces with
   constant label `g`. The pieces with `g` in `H_n` lie in `[[R_n]]`. The
   remaining pieces have mass tending to `0` by dominated convergence, and
   together with `R_n` they generate `E`.
3. **Dichotomy.** Let `c` be the constant relative cost. Then
   `C(a) <= C(R_0) + c`. If this is finite, step 2 forces `c = 0`.
4. **Bernoulli.** Put `(Tx)_gamma = x_{theta^{-1} gamma}`. For freeness, a
   fixed point of `beta(g)`, `g != 1`, is constant on infinitely many
   nontrivial orbits, which is a null event.
5. **Gamma_mal shift.** `b_k -> b_{k+1}` respects
   `b_k = b_{k+1} a b_{k+1}^{-2}`. It maps the basis of `H_k` to the basis of
   `H_{k+1}`, so it is injective. It is onto because
   `b_1 = theta(b_1 a b_1^{-2})`.
