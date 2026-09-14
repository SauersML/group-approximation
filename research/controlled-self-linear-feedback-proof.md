---
rg: 2
id: controlled-self-linear-feedback-proof
kind: route
title: Straighten one block with the certificate-fiber theorem and peel the tail systems downward
target: controlled-self-linear-feedback-ca-are-surjunctive
requires:
  - nonlinear-certificate-fibers-are-all-surjective-or-all-strict
artifacts:
  - research/artifacts/three-factor-audit-and-controlled-feedback-2026-09-12.md
---

**Two-block lemma.** Let `F(X,Y) = (L_Y X, V(X,Y))`, where `L_Y` is additive
in `X` with local controllers. Assume `Y -> V(0,Y)` is surjective and one
`L_(Y_0)` is bijective. If `F` is injective, then `F` is surjective.

- If `L_Y X = 0`, pick `Y'` with `V(0,Y') = V(X,Y)`. Then `F(X,Y) = F(0,Y')`,
  so `X = 0`, and every `L_Y` is injective.
- `E(X,Y) = (L_Y X, Y)` is injective, leaves `Y` unchanged, and has a
  bijective fiber at `Y_0`. By the prerequisite it is bijective, and by
  Curtis–Hedlund–Lyndon its inverse is a cellular automaton.
- `F o E^(-1)` leaves `L_Y X` unchanged. Its zero fiber `Y -> V(0,Y)` is
  surjective, so the prerequisite makes `F o E^(-1)`, and then `F`, surjective.

**Peeling.** Let `S_a` be rows `a, ..., r` of `F` with the blocks before `a`
set to zero.

- `F(0, X_(>=a)) = (0, S_a(X_(>=a)))`, because each earlier row is linear in
  its own vanishing block. So `S_a` is injective.
- `S_r` is the bijective constant part.
- For `a < r`, row `a` of `S_a` is `L_Y X_a` with invertible `L_0`, and
  `S_a(0,Y) = (0, S_(a+1)(Y))`. Downward induction and the lemma make every
  `S_a` bijective, and `S_1 = F`.

Full proof in section 2 of the artifact.
