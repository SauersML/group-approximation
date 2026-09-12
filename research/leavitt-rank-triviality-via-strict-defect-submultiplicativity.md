---
rg: 2
id: leavitt-rank-triviality-via-strict-defect-submultiplicativity
kind: route
title: A strict deficit from independence contradicts near-minimal multiplicativity, so the binary Leavitt unit group has no nontrivial characteristic-two rank model
target: non-linear-sofic-group
requires:
  - leavitt-disjoint-cylinder-defects-strictly-submultiplicative
  - near-minimal-defect-models-have-multiplicative-cylinder-defects
  - leavitt-rank-model-defect-gap-on-fixed-point-free-quotients
artifacts:
  - research/artifacts/two-root-defect-descent-gap-2026-09-12.md
---

Artifact Section 5.

1. **Positive infimum.** Suppose a nontrivial characteristic-two rank model of
   `R^x = L_(F_2)(1,2)^x` exists. Its fixed-point-free quotient is nontrivial
   (`leavitt-rank-model-defect-gap-on-fixed-point-free-quotients`). So the infimum `c_*` of
   normalized defects over nontrivial fixed-point-free models is taken over a nonempty set, and
   the gap makes it positive.
2. **Near-minimal model.** Choose such a model with `delta <= (1+eps) c_*`. By
   `near-minimal-defect-models-have-multiplicative-cylinder-defects`,
   `rk(D_A D_B) >= c_* delta >= delta^2/(1+eps)`.
3. **Contradiction.** Strict submultiplicativity gives `rk(D_A D_B) <= theta delta^2`. That is
   impossible once `eps < 1/theta - 1`. So every characteristic-two rank model of `R^x` is trivial.
4. **Payoff.** An `F_2`-linear sofic approximation of the infinite group `R^x` gives a nontrivial
   homomorphism into a rank ultraproduct over `F_2`. So `R^x` is not `F_2`-linear sofic, which
   exhibits a non-linear-sofic group.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 8.4, as a route conditional on the open strict submultiplicativity claim of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
