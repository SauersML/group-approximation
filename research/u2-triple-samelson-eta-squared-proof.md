---
rg: 2
id: u2-triple-samelson-eta-squared-proof
kind: route
title: Naturality of the Samelson product turns the order-two commutator into eta squared, and a split half-smash detects it on T^2 x S^3
target: u2-triple-samelson-class-three-stage
requires:
  - samelson-circle-sphere-product-has-order-n
artifacts:
  - research/artifacts/stw59-samelson-orders-and-wedged-arms-2026-09-11.md
---

At n=2 the prerequisite gives <alpha, omega> = omega o eta_3, since
pi_4 SU(2) -> pi_4 U(2) is an isomorphism.

The commutator map of alpha and omega o h is the commutator map of alpha
and omega precomposed with 1 x h, so <alpha, omega o h> = <alpha,omega> o (1 ∧ h).
With h = eta_3 this gives <alpha, <alpha,omega>> = omega o eta_3 o eta_4.
Toda: eta_3 eta_4 generates pi_5 S^3.

The triple commutator vanishes on {1} x Y with Y = S^1 x S^3, so it factors
through Sigma(Y_+) ≃ S^1 v Sigma Y. That retract pair has a null Puppe
connecting map, so [Sigma(Y_+), U(2)] -> [S^1 x Y, U(2)] is injective. The
collapse Sigma Y -> S^5 has a homotopy section by the suspension splitting
of products, so pi_5 U(2) injects. The class is therefore nonzero.
