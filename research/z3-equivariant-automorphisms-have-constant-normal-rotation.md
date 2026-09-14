---
rg: 2
id: z3-equivariant-automorphisms-have-constant-normal-rotation
kind: claim
title: A Z_3-equivariant polynomial automorphism of A^3 over F_2 rotates the normal plane of the fixed line by one constant
distinct_from:
  z3-level-preserving-automorphisms-rotate-uniformly: that constrains automorphisms that fix the level s up to translation, on the free Boolean orbits; this holds for every equivariant automorphism and records the rotation along the fixed line of the shift.
  order-three-equivariant-plane-automorphisms-are-linear: that concerns automorphisms of the plane commuting with an order-three element; this concerns automorphisms of A^3 and their derivative along the fixed line.
artifacts:
  - research/artifacts/z3-normal-rotation-and-eigen-hyperplane-rigidity-2026-09-12.md
---

**ESTABLISHED** (proof in Section 1 of the artifact). Independently re-derived by `w3-vf-nonlinear`
(PASS, 235c43220c, `research/artifacts/w3-vf-nonlinear-verification-2026-09-12.md` Section 4).

Let `R` be the cyclic shift on `A^3` over `F_2`, and let `T` be a polynomial automorphism over `F_2`
with `T o R = R o T`. Over `F_4` use `s = x_0+x_1+x_2`, `u = x_0 + omega x_1 + omega^2 x_2` and its
conjugate `ubar`. The fixed line of `R` is `Lambda = {u = ubar = 0}`. Then:
- `T(Lambda) = Lambda`, and `T` acts on `Lambda` as `s -> s + b` with `b` in `F_2`;
- along `Lambda`, `dT_u/du` is one constant `lambda(T)` in `F_4^x`, and `dT_u/dubar = 0`;
- `lambda` is a homomorphism from the equivariant automorphism group to `F_4^x`.

The proof is weight bookkeeping along `Lambda`, plus constancy of the Jacobian determinant: the
normal derivative is a polynomial in `s` with no roots.
