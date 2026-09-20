---
rg: 2
id: fpbs-max-cost-finite-index-scaling-is-coset-descent-proof
kind: route
title: Identify Bernoulli restricted to H as Bernoulli, induce the coset product to the section X x {H}, and squeeze by finite-index star repair and maximality
target: fpbs-max-cost-finite-index-scaling-is-coset-descent
requires:
  - fpbs-bernoulli-maximal-cost
  - abert-weiss-free-actions-weakly-contain-bernoulli
  - cost-is-constant-on-weak-equivalence-classes
  - fpbs-normalized-cost-induction-input
  - fpbs-finite-index-star-relative-cost
  - fpbs-gaboriau-l2-betti-normal-subgroup-and-finite-index
  - fpbs-abert-nikolov-rank-gradient-equals-profinite-cost
  - fpbs-burnside-common-upper-cost
artifacts:
  - research/artifacts/fpbs-max-cost-finite-index-scaling-2026-09-17.md
---

The route has five steps:

1. **Bernoulli restricted to H.** Relabel the coordinates along
   `H x T -> Gamma`. This shows that `b_Gamma|H` is an `H`-Bernoulli shift
   with base `A^T`. Abért–Weiss together with Kechris monotonicity gives every
   Bernoulli shift the maximal cost, so `C(b_Gamma|H) = C^*(H)`.
2. **Induction.** The set `A^Gamma x {H}` is a complete section of `Y` of
   measure `1/q`. Its restricted relation is the orbit relation of
   `b_Gamma|H`. Gaboriau's induction formula then gives
   `C(Y) - 1 = (C^*(H) - 1)/q`.
3. **Squeeze.** Maximality gives `C(Y) <= C^*(Gamma)`. Finite-index star
   repair on `R_{b|H} <= R_b` gives `C^*(Gamma) <= C^*(H)`.
4. **Necessity.** Fixed price gives `C(Y) = C(b)`. The Betti target together
   with `beta_1(H) = q beta_1(Gamma)` gives (i).
5. **Rank gradients and calibration.**
   - The bound `C^*(H) <= d(H)` and Abért–Nikolov sandwich every Farber rank
     gradient between `rho` and `C^* - 1`.
   - On `B(2,n)`, the common upper cost turns (i) into `c_n = 1`.

The artifact contains the written deduction. It is not a formal verification.
