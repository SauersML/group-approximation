---
rg: 2
id: projective-schur-class-extension-proof
kind: route
title: Extend the projective homomorphism across the adjunction and use naturality of evaluation
target: projective-unitary-classes-vanish-on-schur-kernel
requires: [nonsingular-adjunction-preserves-approximation-radicals]
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

Section S2 of the artifact. `T = (prod U(d_n))/(N . prod U(1))` is itself an
algebraic quotient of a unitary product, so the prerequisite's extension
lemma factors `phi` through `X`. Pullback of extensions and the
universal-coefficient evaluation are natural, so `beta_phi = beta_(phi') o q_*`.
For finite `Q`, the twisted regular representation of a normalized cocycle
realizes each class in `PU(|Q|)`, and `U(1)` separates the finite group
`H_2(Q)`.
