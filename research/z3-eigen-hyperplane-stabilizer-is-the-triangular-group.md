---
rg: 2
id: z3-eigen-hyperplane-stabilizer-is-the-triangular-group
kind: claim
title: A Z_3-equivariant automorphism of A^3 over F_2 preserves the cone u ubar = 0 iff it has the triangular form (s + f(v), lambda v)
distinct_from:
  z3-level-preserving-automorphisms-rotate-uniformly: that shows level-preserving automorphisms have the form (s + b, lambda v) and that the triangular group has uniform shadows; this identifies the triangular group as the full stabilizer of the cone u ubar = 0, which contains maps that do not preserve the level, such as (s + u ubar, v).
  z3-equivariant-automorphisms-have-constant-normal-rotation: that records the rotation along the fixed line for every equivariant automorphism; this forces the triangular form, but only when the cone is preserved.
artifacts:
  - research/artifacts/z3-normal-rotation-and-eigen-hyperplane-rigidity-2026-09-12.md
---

**ESTABLISHED** (proof in Section 2 of the artifact; independent re-derivation requested from
`w3-vf-nonlinear`).

Use the coordinates of `z3-equivariant-automorphisms-have-constant-normal-rotation`, and write
`x = s(1,1,1) + v` with `v` in the 2-dimensional summand `V`. Let `T` be a `Z_3`-equivariant
polynomial automorphism of `A^3` over `F_2`. The following are equivalent:
- `T` maps the quadric cone `C = {u ubar = 0} = {sum x_i^2 + sum_(i<j) x_i x_j = 0}` into itself;
- `T` maps `H = {u = 0}` over `F_4` into itself;
- `T_u = lambda(T) u`;
- `T(s, v) = (s + f(v), lambda v)`, with `f` an `R`-invariant polynomial and `lambda` in `{1, R, R^2}`.

**Proof sketch.**
- A cone-preserving `T` cannot send `H` into `{ubar = 0}`. Otherwise `ubar` divides `T_u`, and the
  normal rotation along the fixed line vanishes.
- If `T` preserves `H`, then `u` divides both `T_u` and `(T^-1)_u`. The cofactors multiply to 1, so
  `T_u = lambda u`.
- Then `T` fixes `F_2[V]` up to `lambda`. An `F_2[V]`-algebra automorphism of `F_2[V][s]` is
  `s -> s + c(v)`.

**Consequence for the Boolean shadow.**
- The triangular group realizes exactly the order-12 group `K` of uniform shadows. `K` has index 3
  among the 36 equivariant permutations of `F_2^3`, so the realized shadow group is `K` or all of
  them.
- So the permutation of `z3-weight-one-rotation-is-not-an-automorphism-shadow` is realizable iff some
  equivariant automorphism has a shadow outside `K`.
- Any realization moves the cone `C`.
