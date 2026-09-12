---
rg: 2
id: signed-thompson-group-has-no-finite-dimensional-representations
kind: claim
title: The signed Thompson group has no nontrivial finite-dimensional representation, so support no-gos needing z to act by -1 do not bind on it
artifacts:
  - research/artifacts/ternary-lift-signed-thompson-crossed-product-2026-09-12.md
---

Let `H = E ⋊ V` be the signed Thompson group inside `L_(F_3)(1,2)^x`, as in
`signed-thompson-algebra-is-odd-measure-crossed-product`:
* `E = {tau_C = 1 - 2 P_C}` is the reflection group of the clopens of Cantor space;
* `V` is Thompson's group.

For every field `k` and every representation `rho : H -> GL_n(k)` with `n` finite, `rho` is trivial.

In particular, no finite-dimensional representation of `H` sends `z = tau_X` to `-1`. So an
obstruction to one-sided pairs or corner solutions that needs a representation with `z -> -1` on the
support group does not apply to the signed Thompson crossed product `F_3[H] eps_-`. Section 9 of the
artifact.
