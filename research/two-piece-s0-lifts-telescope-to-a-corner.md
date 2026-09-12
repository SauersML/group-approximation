---
rg: 2
id: two-piece-s0-lifts-telescope-to-a-corner
kind: claim
title: A two-piece lift of s0 through Thompson units has a unit product with its partner exactly when a corner product is a unit
distinct_from:
  leavitt-inverse-defects-are-visible-or-invisible: that normalizes an arbitrary one-sided pair by a group translate; this is a construction ansatz, with an exact criterion for when its product is a unit
  leavitt-corner-one-sided-lift-exists: that states the lifting problem in a corner where the augmentation no-go is switched off; this reduces the whole-algebra problem, for two-piece lifts, to one invertibility question in the corner over s1t1
  binary-swap-group-lifts-leavitt-matrix-units-with-kernel-gap: that constructs idempotent lifts of the cylinder partition; this uses any such lift, together with two Thompson-type units, and computes the product of the lift pair
artifacts:
  - research/artifacts/binary-visible-lift-two-piece-telescoping-2026-09-12.md
---

Let `A = F_2[R^x]` with `R = L_(F_2)(1,2)` and evaluation `pi`. The data are:
- an idempotent `E^` of `A` with `pi(E^) = s0t0`, and `E1^ = 1 - E^`;
- units `g1, g2` with `g1 s0 = s00`, `g1 P_0 g1^(-1) = P_00`, `g2 s1 = s01` and `g2 P_1 g2^(-1) = P_01`;
- `h = g1^(-1) g2`.

Put `a = [g1]E^ + [g2]E1^` and `b = E^[g1^(-1)] + E1^[g2^(-1)]`.

1. `pi(a) = s0`, `pi(b) = t0`, and `b a = 1 + X + Y`, where `X = E^[h]E1^` and `Y = E1^[h^(-1)]E^` both lie in
   `ker pi`.
2. With `C = E1^[h]E1^` and `C' = E1^[h^(-1)]E1^`, `YX = E1^ + C'C`.
3. `b a` is a unit of `A` if and only if `C'C` is a unit of `E1^ A E1^`. Then `(ba)^(-1) b` is a left inverse of
   `a`, so `a` witnesses `left-invertible-lift-of-s0-in-leavitt-group-algebra`.
4. If `X = 0` or `Y = 0`, then `b a - 1` squares to zero, so `b a` is a unit.
5. `b a - 1` is nilpotent if and only if `YX` is nilpotent.
6. `pi(C)` and `pi(C')` are a proper partial isometry of the corner `P_1 R P_1` and its left inverse. So the
   criterion in item 3 is the visible problem again, one corner down.

Proof: Section 2 of the artifact, route `two-piece-s0-lift-telescoping-proof`.
