---
rg: 2
id: controlled-self-linear-feedback-proof
kind: route
title: Straighten one block with the certificate-fiber theorem and induct on the zero fiber
target: controlled-self-linear-feedback-ca-are-surjunctive
requires:
  - nonlinear-certificate-fibers-are-all-surjective-or-all-strict
artifacts:
  - research/artifacts/three-factor-audit-and-controlled-feedback-2026-09-12.md
---

**Two-block lemma.** Let `F(X,Y) = (L_Y X, V(X,Y))`, where `L_Y` is additive
in `X` with local controllers. Assume `Y -> V(0,Y)` is surjective and one
`L_(Y_0)` is bijective. If `F` is injective, then `F` is surjective.

- **Every `L_Y` is injective.** If `L_Y X = 0`, pick `Y'` with
  `V(0,Y') = V(X,Y)`. Then `F(X,Y) = F(0,Y')`, so `X = 0`.
- **Straighten.** `E(X,Y) = (L_Y X, Y)` is injective and leaves `Y` unchanged,
  with a bijective fiber at `Y_0`. By the prerequisite it is bijective, and
  by Curtis–Hedlund–Lyndon its inverse is a cellular automaton.
- **Zero fiber.** `F o E^(-1)` leaves `Z = L_Y X` unchanged. Its zero fiber
  is `Y -> V(0,Y)`, which is surjective, so the prerequisite makes
  `F o E^(-1)` surjective, and then `F`.

**Theorem.** Induct on the number of blocks.
- **One block.** The controllers are constant and `F` is the bijective
  constant part.
- **Several blocks.** Row 1 is `L_Y X_1` with `L_0` the invertible constant
  part. The other rows at `X_1 = 0` form a smaller system of the same shape,
  injective because `F(0,Y) = (0, V(0,Y))`, and bijective by induction. The
  lemma finishes.

Full proof in section 2 of the artifact.
