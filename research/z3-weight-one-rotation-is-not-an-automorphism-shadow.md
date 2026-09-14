---
rg: 2
id: z3-weight-one-rotation-is-not-an-automorphism-shadow
kind: claim
title: The permutation of {0,1}^(Z_3) rotating only the weight-one orbit is not the shadow of any equivariant polynomial automorphism
distinct_from:
  binary-left-inverse-pairs-need-not-be-formalizable: that is the established witness on the integers, through the bi-orderable leading-term theorem; this is a candidate second witness on a finite group, where that theorem does not apply and the constant-level map is the identity.
  z3-level-preserving-automorphisms-rotate-uniformly: that proves the rigidity for automorphisms preserving the level s; this asks for all equivariant automorphisms, including level-mixing ones.
artifacts:
  - research/artifacts/formalizability-finite-levels-and-z3-rigidity-2026-09-12.md
---

**OPEN.** Let `rho` on `{0,1}^(Z_3)` send `e_i -> e_(i+1)` on the weight-one orbit and fix the other
five points.
- **Rule:** `rho(x)_g = x_(g-1)` when `x` has weight one, and `x_g` otherwise.
- **Claim:** no `Z_3`-equivariant polynomial automorphism of `A^3` over `F_2` has shadow `rho`.
  Equivalently, by `finite-group-formalizability-equals-equivariant-automorphism`, the bijective pair
  `(rho, rho^-1)` is not formalizable.

**Same question as the order-three control.**
- **The link:** complementation `x -> x + 111` commutes with the shift, is a formal affine
  involution, and swaps weights one and two. It conjugates `rho` into a rotation of the weight-two
  orbit only. The order-three control `C(x)_j = x_j + x_j x_(j+1) + x_(j+1) x_(j+2)` is such a
  rotation; it is the instance in `own-block-local-bijection-rows-peel` (gk-free-neg).
- **Consequence:** the two are formalizable together or not at all. A proof here also shows that a
  peelable own-block row need not be formalizable.

## Attempts

- **Level-preserving representatives are dead** (`z3-level-preserving-automorphisms-rotate-uniformly`).
  Every automorphism with `T*(s) = s + b` rotates both free orbits uniformly, whatever its nonlinear
  dependence on `v`.
- **Where a realization must live.** It has to mix levels: `T*(s) - s` is a nonconstant `Z_3`-invariant
  polynomial vanishing on all eight Boolean points. Shears `(s + f(v), v)`, rotations, translations
  and all their composites have uniform shadows.
- **Linear commutant.** In Fourier coordinates over `F_4` (gk-free-neg), any representative acts on
  each Boolean level `u_0 = c` by `u_1 -> lambda_c u_1`. The whole question is interpolating
  `lambda_0 = 1` and `lambda_1 = omega^(±1)` across the level variable. The linear commutant over
  `F_2[s]` is `F_4[s]`, whose units are `F_4^×`.
- **`s`-controlled maps on `V`:** additive candidates such as `u -> u + omega^2 s u^4` are not
  injective over `F̄_2` for `s ≠ 0`.
- **Invariant-ratio functions** `u o T / u` read the rotation at free Boolean points, but give no
  contradiction.
- **What is missing:** a structure theorem for `Z_3`-equivariant automorphisms of `A^3` in
  characteristic 2 that covers level-mixing maps.
- **Scope under stabilization.** With a second track, `V` has multiplicity two, and non-uniform
  equivariant automorphisms such as `(s, v_1 + s v_2, v_2)` exist. So this is a one-track test, and it
  says nothing about `injective-binary-automata-are-stably-formalizable`.

Artifact, Sections 3–5.
