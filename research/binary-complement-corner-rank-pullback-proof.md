---
rg: 2
id: binary-complement-corner-rank-pullback-proof
kind: route
title: Pull rank functions back along the halving homomorphism into the complement corner, and restrict the other way using simplicity
target: binary-complement-corner-rank-functions-pull-back-to-units
requires:
  - simple-group-rank-functions-are-augmentation-or-detecting
  - binary-leavitt-unit-group-is-simple
artifacts:
  - research/artifacts/binary-cyclic-corner-complement-states-2026-09-12.md
---

Artifact Proposition C.

1. **Pullback.** `ψ'(x) = f D(x)` is a unital ring homomorphism `F_2[G] -> T`, so `N ∘ ψ'` is a Sylvester
   matrix rank function.
2. **The value at `g`.**
   - `ψ'(1 - [g]) = (f_(K_3) + f_(K_4))(1 - [D(g)])` is invertible in the block `(f_(K_3) + f_(K_4)) F_2[A_9]`.
   - So its rank is `N(f_(K_3) + f_(K_4))`.
   - The three idempotents `f_K` inside `f` are orthogonal and pairwise equivalent in `T` (nine-cylinder
     permutation units), so the rank is `2/3`.
   - The dichotomy then makes the pullback detecting.
3. **Restriction.**
   - `1 - [g] = (1 - [g]) f`, so `rk(f) = 0` forces `g` into the normal subgroup `N_rk`.
   - Simplicity of `G` then forces `rk = rk_ε`.
   - Otherwise `rk/rk(f)` on matrices over `T` is normalized.
