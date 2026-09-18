---
rg: 2
id: kernel-polynomiality-from-no-root-free-overgroup
kind: route
title: The compressor-stable kernel statement is the Laurent case of the stability-free overgroup theorem
target: kt-compressor-stable-kernel-overgroups-are-polynomial
requires:
  - sl-r-polynomial-has-no-root-free-laurent-overgroup
---

Let `H` be as in the target. That is, `SL_r(A) <= H <= SL_r(R)`, where
`A = F_q[x_1,…,x_d]` and `R` is its Laurent ring; `H` is `Mon`-stable; and
`H ∩ U_12(R) = U_12(A)`.

The Laurent case of `sl-r-polynomial-has-no-root-free-laurent-overgroup` states: "every
subgroup `H` with `SL_r(A) <= H <= SL_r(R)` and `H ∩ U_12(R) = U_12(A)` equals
`SL_r(A)`". Its hypotheses are:

* `A = F_q[x_1,…,x_d]` is a UFD;
* `R = A[1/(x_1⋯x_d)]`;
* `r >= 3`.

All three hold here. So `H = SL_r(A)`, which is the target.

The `Mon`-stability hypothesis and the bound `d >= 3` are never used. The target
therefore holds for every `d >= 1` and for every overgroup, stable or not.

Downstream effects:

* The route `kt-sandwich-from-kernel-polynomiality` now has all its requirements
  established. It gives `kt-compressor-stable-polynomial-content-overgroups-are-gamma`.
* That makes `kt-pair-floor-reduces-to-wreath-model-via-compressor-sandwich` live toward
  `hyperlinear-wreath-model`, provided its other requirements are met.
