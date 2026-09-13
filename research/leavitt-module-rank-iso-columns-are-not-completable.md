---
rg: 2
id: leavitt-module-rank-iso-columns-are-not-completable
kind: claim
title: At module rank m, no column of an isomorphism between free L_K(m,n)-modules of different ranks is completable, so there is no free coordinate
---

Let `R` be a unital ring whose free modules satisfy

```text
(IBN-m)   R^i ≅ R^j  ⟺  i = j,  or  i, j ≥ m and i ≡ j (mod n − m)
```

for some `1 ≤ m < n`. Every Leavitt algebra `R = L_K(m, n)` does, by
`ara-goodearl-leavitt-mn-monoid-is-one-relator`. Let `M ≠ N`, `X ∈ M_{N×M}(R)` and `Y ∈ M_{M×N}(R)` with
`XY = 1_N` and `YX = 1_M`.
- If `min(M, N) = m`, no column of `X` lies in `GL_N(R)·e_1`, and no column of `Y` lies in `GL_M(R)·e_1`. In
  particular neither matrix has a column equal to a standard basis vector: there is no free coordinate.
- If `min(M, N) < m`, no such `X, Y` exist.

**Consequence for the MF band.** At `N = m`, every conjugation `g ↦ XgY` of `GL_M(R)` onto `GL_m(R)` sends
elementary matrices to transvections `1 + x_i r y_j` whose column `x_i` cannot be moved to `e_1` by any invertible
matrix. So neither Suslin's conjugation argument nor the free-coordinate argument of
`non-ibn-ring-el-n-full-mf-radical-above-module-rank` can place the image of `EL_M(R)` inside `EL_m(R)`.

**Review (un-verify-open, 2026-09-13, `research/artifacts/un-review-open-2026-09-13-part2.md`): PASS. Complements of x_i R of rank M−1 and, after completion, N−1 contradict (IBN-m) at minimum m−1; model tests re-checked.**
