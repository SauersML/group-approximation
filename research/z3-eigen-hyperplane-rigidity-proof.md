---
rg: 2
id: z3-eigen-hyperplane-rigidity-proof
kind: route
title: Irreducibility, divisibility by u for the automorphism and its inverse, and translations of F_2[V][s]
target: z3-eigen-hyperplane-stabilizer-is-the-triangular-group
requires:
  - z3-equivariant-automorphisms-have-constant-normal-rotation
artifacts:
  - research/artifacts/z3-normal-rotation-and-eigen-hyperplane-rigidity-2026-09-12.md
---

Artifact Section 2.
1. **Cone ⇒ hyperplane.** `T(H)` is irreducible inside `H ∪ Hbar`. If it lay in `Hbar`, `ubar` would
   divide `T_u`, and the normal rotation of the prerequisite would vanish.
2. **Hyperplane ⇒ `T_u = lambda u`.**
   - `T(H) = H`, so `T_u = u beta` and `(T^-1)_u = u beta'`.
   - Then `u = u beta (beta' o T)`, so `beta` is a unit, i.e. the constant `lambda(T)`.
3. **`T_u = lambda u` ⇒ triangular.** `(s, lambda^-1 v) o T` fixes `F_2[V]` pointwise. Its action on
   `s` is an `F_2[V]`-algebra automorphism of `F_2[V][s]`, hence `s -> s + c(v)` with `c` invariant.
4. **Triangular ⇒ cone.** It multiplies `u` by `lambda`.
