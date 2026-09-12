---
rg: 2
id: commutant-distortion-from-strict-defect-submultiplicativity
kind: route
title: A strict deficit for products of disjoint cylinder defects is a commutant rank distortion at the element D_A
target: some-commutant-element-distorts-defect-range-rank
requires:
  - leavitt-disjoint-cylinder-defects-strictly-submultiplicative
  - leavitt-rank-model-defect-gap-on-fixed-point-free-quotients
artifacts:
  - research/artifacts/halving-expansion-and-commutant-faithfulness-2026-09-12.md
---

Artifact Proposition 2.3(2).

* Take `U = B`, `Theta` the frame triple of the cylinder `B0`, and `Z = D_A` with `A` disjoint from `B` and
  `A ∪ B` proper. `D_A` commutes with `sigma(G_B)`.
* By Fact 1.2 of the descent artifact, `rk(D_(B0) D_A) = f(2)`. Strict submultiplicativity gives
  `f(2) <= theta delta^2`.
* So `delta rk(Z) - rk(D_(B0) Z) >= (1 - theta) delta^2`. The gap gives `delta >= c_0` on nontrivial
  fixed-point-free models, so the distortion is at least `kappa delta` with `kappa = (1 - theta) c_0`.
