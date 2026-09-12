---
rg: 2
id: leavitt-hs-stable-from-no-factorial-canonical-model
kind: route
title: Exclude factorial canonical models and upgrade any model to a factorial one
target: leavitt-steinberg-hs-stable
requires: [leavitt-unit-has-no-factorial-canonical-model, leavitt-unit-hyperlinear-gives-factorial-canonical-model, leavitt-unit-hs-stable-iff-nonhyperlinear]
---

Suppose `L^x` were hyperlinear.
* The existence input gives a canonical model with factorial global
  commutant, which the nonexistence claim forbids. So `L^x` is
  nonhyperlinear.
* By `leavitt-unit-hs-stable-iff-nonhyperlinear` it is normalized-HS stable.
  This is `St_5(L)` stability, since `St_5(L) = L^x`.

This is the single-use form of the heat-rounding route
`leavitt-hs-stable-from-channel-rounding`.
* The rounding premise is needed only in the native corner of factorial models,
  where `factorial-leavitt-models-have-external-corner-commutants` shows it
  is equivalent to nonexistence of such models.
* The selection use of rounding is replaced by the open existence input. That
  input is an operator-algebra question about the property (T) factor
  `L(L^x)` alone.
