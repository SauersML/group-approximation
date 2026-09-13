---
rg: 2
id: commutators-ko-eta-powers-proof
kind: route
title: Hodgkin's primitive generators die under the commutator, and Wood's sequence adds one eta per bracket, by induction over smash factors
target: nested-commutators-pull-ko-of-unitary-groups-into-eta-powers
requires: []
artifacts:
  - research/artifacts/class-four-lambda-mod-eight-trapping-part4-2026-09-13.md
---

Part 4, Section 10.

(1) By Hodgkin, K^*(U(N)) is exterior on the primitive classes
beta(lambda^i). For a primitive p, mu^* p = p (x) 1 + 1 (x) p and inv^* p = −p,
so c^* p = 0. The map c^* is multiplicative, so c^* kills KU~^*(U(N)).

(2) Take z in KO^*(X ∧ G) with G = U(N). Künneth holds for KU^*(X ∧ G) and
KU^*(X ∧ G ∧ G), because K^*(G) is free. So the complexification of
(1_X ∧ c)^* z is (1 (x) c^*)(z_C) = 0. Wood's exact sequence
KO^{*+1} -eta-> KO^* -> KU^* then gives (1_X ∧ c)^* z = eta·z'.

(3) Write c_j = c o (1 ∧ c_{j−1}). Apply (2), then the induction hypothesis
with X' = X ∧ G to z'. This gives eta^{j−1}. For a nested commutator on M,
f = c_j o (g_{j−1} ∧ ... ∧ h) o Delta, so f^* z lies in eta^{j−1}·KO^*(M).

(4) Mod 2: H^*(U(N); Z/2) is exterior on primitive classes, so the same
computation gives c^* = 0 on reduced classes.
