---
rg: 2
id: root-character-depth-log-dimension-proof
kind: route
title: The Heisenberg group x_13, x_32, x_12 moves each root eigen-character through |B/J_χ| orthogonal eigenspaces
target: root-character-nonunit-depth-at-most-log-q-dimension
requires: []
artifacts:
  - research/artifacts/nh-h1-quantitative-2026-09-12.md
---

Full derivation in §2 of the artifact.

- **Item 1.**
  - Suppose `Σ_(i0 <= i < k) c_i e_nu z^i ∈ J_χ` with `c_i ∈ F_q` and `c_(i0) ≠ 0`.
  - Write it as `e_nu z^(i0) u` with `u = c_(i0) + z w`. In each local factor of `A_nu` some `x_j` lies in the
    maximal ideal, so `z` is nilpotent on `A_nu`, and the `A_nu`-component of `u` is a unit.
  - Multiply by an element whose `A_nu`-component is its inverse. Since `J_χ` is an ideal, `e_nu z^(i0) ∈ J_χ`.
  - Then `e_nu z^(k-1) B ⊆ J_χ ⊆ ker χ`, so `χ_nu` is trivial on `z^(k-1) R_+`. That contradicts
    `depth_nu(χ) = k`.
- **Item 2.**
  - Put `X(b) = π(x_13(b))` and `Y(c) = π(x_32(c))`.
  - The Steinberg relations give `[x_12, x_13] = [x_12, x_32] = 1` and `[x_13(b), x_32(c)] = x_12(bc)`, which
    uses `r >= 3`. So `V_χ` is invariant under `X` and `Y`, and on `V_χ`
    `X(b) Y(c) = χ(bc) Y(c) X(b)`.
  - The commuting unitaries `X(B)` have a joint eigenvector `v ≠ 0` in `V_χ`, with character `λ`. Then
    `Y(c)v ≠ 0` has joint eigencharacter `b -> λ(b)χ(bc)`.
  - These characters coincide for `c, c'` iff `χ(b(c - c')) = 1` for all `b`, i.e. iff `c - c' ∈ J_χ`, because
    `B` is commutative.
  - Distinct joint eigencharacters of a commuting unitary family have orthogonal eigenspaces. So
    `dim V_χ >= |B/J_χ|`. The same argument runs inside any irreducible constituent whose `x_12`-spectrum
    contains `χ`.
- **Item 3.**
  - `μ({χ}) = dim V_χ / N`.
  - Combine items 1 and 2, and apply item 2 inside the irreducible constituent carrying `χ`.
