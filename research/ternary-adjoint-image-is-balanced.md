---
rg: 2
id: ternary-adjoint-image-is-balanced
kind: claim
title: Both multiplications take the augmentation value on the adjoint image of the ternary projective group algebra
distinct_from:
  projective-ternary-klein-idempotent-is-full: that asks for a corner equation in the group algebra; this is a linear invariant of that algebra's image in R (x) R^op, which every witness must respect.
artifacts:
  - research/artifacts/klein-target-balanced-invariant-2026-09-12.md
---

Let `k = F_3`, `R = L_k(1,2)`, `PG = R^x/{±1}` and `Q = R (x)_k R^op`, and let
`rho([g]) = g (x) (g^-1)^op` be the adjoint evaluation. Define linear maps `mu, mu' : Q -> R` by
`mu(a (x) b^op) = ab` and `mu'(a (x) b^op) = ba`.

Every `T` in `rho(k[PG])` satisfies `mu(T) = mu'(T) = eps(T) 1`, where `eps` is the augmentation. The
balanced set `N = {T : mu(T) = mu'(T) in k 1}` is a unital subalgebra of `Q`, and `T -> mu(T)` is a
`k`-algebra character of `N`.

`mu(T) = T(1)` is the invariant line already recorded for this image; `mu'` is the second invariant.
Proof: Section 2 of the artifact.
