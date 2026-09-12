---
rg: 2
id: order-three-equivariant-plane-automorphisms-are-linear
kind: claim
title: A polynomial automorphism of the plane commuting with an order-three linear map without eigenvectors is a scalar of K[R]
artifacts:
  - research/artifacts/formalizability-finite-levels-and-z3-rigidity-2026-09-12.md
---

Let `K` be a field, and let `R` in `GL_2(K)` satisfy `R^2 + R + 1 = 0`, with `x^2 + x + 1` irreducible
over `K`. Every polynomial automorphism of `A^2_K` commuting with `R` has the form `v -> lambda v` with
`lambda` in `K[R]^×`. Over `F_2` these are exactly `1, R, R^2`.

*Why.*
- **Fixed vertex.** `R` fixes only the `Aff`-vertex of the Bass–Serre tree. Fixing a neighbour would
  make a conjugate of `R` lie in `Aff ∩ Tri`, giving `R` an eigenvector over `K`.
- **Centralizer.** A commuting automorphism preserves that fixed vertex, so it is affine. Its
  translation part is `R`-fixed, hence 0, and its linear part lies in the centralizer `K[R]`.

Artifact, Section 2, Theorem 3.
