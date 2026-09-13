---
rg: 2
id: every-f-infinity-group-non-proper-bnsr-by-type-f-dichotomy
kind: route
title: "Non-proper BNSR inclusion for all F_infinity groups: split by whether a finite classifying space exists"
target: every-f-infinity-group-has-a-non-proper-bnsr-inclusion
requires:
  - type-f-bnsr-invariants-stabilize-at-dimension
  - non-type-f-f-infinity-groups-have-a-non-proper-bnsr-inclusion
---

A group of type `F_∞` either has a finite classifying space or it does not.

- In the first case `type-f-bnsr-invariants-stabilize-at-dimension` gives
  `Σ^n(G) = Σ^{n+1}(G)`, where `n` is the dimension of a finite classifying
  space.
- In the second case `non-type-f-f-infinity-groups-have-a-non-proper-bnsr-inclusion`
  gives some equality `Σ^m(G) = Σ^{m+1}(G)`.

The dichotomy is exhaustive, so both prerequisites together give the target.
The first prerequisite is established; the open content is the second.
