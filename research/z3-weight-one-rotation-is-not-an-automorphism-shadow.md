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
  - research/artifacts/z3-normal-rotation-and-eigen-hyperplane-rigidity-2026-09-12.md
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
- **Stabilizer of the eigen-hyperplane** (w3-nonformal,
  `z3-eigen-hyperplane-stabilizer-is-the-triangular-group`).
  - An equivariant automorphism preserves the quadric cone `C = {u ubar = 0}` iff it has the form
    `(s + f(v), lambda v)`. That group realizes exactly the order-12 shadow group `K`.
  - `K` has index 3 among the 36 equivariant permutations of `F_2^3`, so the realized shadow group is
    `K` or all of them.
  - So a realization exists iff some equivariant automorphism has a shadow outside `K`, and every
    realization moves `C`.
- **Normal rotation** (w3-nonformal, `z3-equivariant-automorphisms-have-constant-normal-rotation`).
  - Every equivariant automorphism rotates the normal plane of the fixed line by a constant
    `lambda(T)`, and `lambda` is a homomorphism to `F_4^×`.
  - Composing with a power of the shift normalizes a realization to `lambda = 1`.
  - No link is known between `lambda` and the rotations at free Boolean points.
- **Line crossing** (w3-nonformal, artifact
  `z3-normal-rotation-and-eigen-hyperplane-rigidity-2026-09-12.md`, Section 3).
  - Normalize `T` to preserve both free orbits, rotating `O_i` by `R^(r_i)`.
  - On the rational line `gamma(t) = (t, t+1, t+1)` from `011` to `100`, the polynomial
    `p(t) = T_u(gamma(t))` has `p(0) = omega^(r_2)` and `p(1) = omega^(r_1)`. So a realization needs
    `p` nonconstant, and `gamma` must meet `T^-1(u = 0)` at a point outside `A^3(F_2)`.
  - Equivalently, `r_2 - r_1` is the `Z_3`-torsor monodromy along the rational loop formed by `gamma`
    and `T(gamma)` in `(A^3 - Lambda)/Z_3`.
  - No invariant is known that computes this monodromy outside the triangular group.
- **What is missing:** a structure theorem for `Z_3`-equivariant automorphisms of `A^3` in
  characteristic 2 that move the cone `C`.
- **Scope under stabilization.** With a second track, `V` has multiplicity two, and non-uniform
  equivariant automorphisms such as `(s, v_1 + s v_2, v_2)` exist. So this is a one-track test, and it
  says nothing about `injective-binary-automata-are-stably-formalizable`.
- **With one ancilla track `rho` IS realized** (w4-z3-rotation, `z3-equivariant-permutations-are-stably-realizable`,
  artifact `z3-rotation-stable-realization-2026-09-12.md`).
  - **Mechanism.** Commute a level flip controlled by the line `l` with the shear word of `A in SL_2(F_4)`
    controlled by `s_1`, where `A` fixes `l` with eigenvalue `omega`. The result rotates `l` by
    `omega^2` at `s_1 = 1` and by `omega` at `s_1 = 0`, and fixes everything else.
  - **Assembly.** Take the product over the five lines, compose with the diagonal shift and the
    level-controlled `diag(omega^2, omega)`. The shadow is `u_1 -> omega^(s_1) u_1`, which is `rho x id`.
  - **Scope.** Every equivariant permutation of `{0,1}^(Z_3)` is stably formalizable with one track,
    so this claim is only a one-track question. The analogue of `lambda` that survives is the constant
    normal determinant `delta in F_4^×`, and it does not constrain shadows.
  - **Why the one-track case differs.** On one track, `V` has multiplicity one, so no controlled flip
    can separate lines. That is the room the ancilla adds.

Artifact, Sections 3–5.
