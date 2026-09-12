---
rg: 2
id: order-three-equivariant-plane-automorphisms-linear-proof
kind: route
title: The elliptic order-three element fixes a single vertex, so its centralizer is affine
target: order-three-equivariant-plane-automorphisms-are-linear
requires:
  - automorphisms-of-the-affine-plane-are-an-amalgam
artifacts:
  - research/artifacts/formalizability-finite-levels-and-z3-rigidity-2026-09-12.md
---

Artifact, Section 2, Theorem 3.
1. **A single fixed vertex.** `R` lies in `Aff`, so it fixes the vertex `v_A`. The fixed set of a
   tree automorphism without inversion is a subtree. So a second fixed vertex would give a fixed
   neighbour `g.v_T` with `g` in `Aff`, and then `g^-1 R g` would lie in `Aff ∩ Tri`. Those maps
   preserve the direction `e_2`, so `R` would have an eigenvector, a root of `x^2 + x + 1` in `K`.
2. **Commuting automorphisms are affine.** A commuting automorphism preserves `Fix(R) = {v_A}`, so it
   lies in `Aff`: `v -> Av + c`, with `AR = RA` and `Rc = c`.
3. **The affine map is `lambda v`.** `(R - 1)(R + 2) = -3` is invertible, since characteristic 3 is
   excluded, so `c = 0`. The centralizer of `R` is the field `K[R]`, so `A` lies in `K[R]^×`.
