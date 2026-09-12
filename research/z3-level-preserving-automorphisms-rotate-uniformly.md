---
rg: 2
id: z3-level-preserving-automorphisms-rotate-uniformly
kind: claim
title: A Z_3-equivariant polynomial automorphism of A^3 over F_2 that preserves the level rotates every free Boolean orbit by the same power of the shift
artifacts:
  - research/artifacts/formalizability-finite-levels-and-z3-rigidity-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

Let `Z_3` act on `A^3` over `F_2` by cyclic shift. Write `x = s(1,1,1) + v`, where `s = x_0 + x_1 + x_2`
and `v` lies in the 2-dimensional summand `V`, on which the shift acts by `R`.

**Statement.** Let `T` be a `Z_3`-equivariant polynomial automorphism with `T*(s) = s + b`. Then
`T(s,v) = (s + b, lambda v)` with `lambda` in `{1, R, R^2}`. This allows arbitrary nonlinear
dependence on `v` and on `s`.

**Consequences.**
- The Boolean shadow rotates both free orbits, weights one and two, by the same power of the shift.
- The group of maps `(s + f(v), lambda v)`, with `f` an `R`-invariant polynomial, also has only
  uniform shadows.

*Why.* Over `K = F_2(s)`, `v -> Phi(s,v)` is an `R`-equivariant automorphism of `A^2_K`. So
`Phi = lambda(s) v` with `lambda(s)` a unit of `F_2[s][R] ≅ F_4[s]`, which is a constant.

Artifact, Section 3, Theorem 4.
