---
rg: 2
id: stw99-l-rotation-oinfty-scaled-k-theory
kind: claim
title: A theta tensor O infinity is a UCT Kirchberg algebra with the same scaled K-theory and a canonical K1 basis
artifacts:
  - research/artifacts/stw99-l-six-kirchberg-loops-2026-09-05.md
---

For irrational `theta`, `D = A_theta (x) O_infinity` is a unital UCT
Kirchberg algebra with

```text
K_0(D) = Z [1_D] (+) Z q,     K_1(D) = Z [U (x) 1] (+) Z [V (x) 1],
```

where `U, V` are the canonical unitaries of `A_theta` and `q` is any
chosen complement of the primitive class `[1_D]`.  So `D` has scaled
graded K-theory `(Z^2, (1,0), Z^2)`: the same invariant as the model
`A = B (x) B`, and `pi_1(Aut(D)) = Z^6`, the value STW state for
`A_theta`.

The `K_1` basis is the concrete one: in the odd Pimsner--Voiculescu
sequence for `A_theta = C(T) x_theta Z`, the connecting maps `1 - alpha_*`
vanish because the rotation is homotopic to the identity, so `[U]` is the
image of the circle's `K_1` generator and `[V]` maps under the boundary
to the circle's unit class.  Tensoring with `O_infinity` changes neither
the groups nor these generators.
