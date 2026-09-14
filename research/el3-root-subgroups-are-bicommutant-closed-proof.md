---
rg: 2
id: el3-root-subgroups-are-bicommutant-closed-proof
kind: route
title: Direct centralizer computation for the root, row and column subgroups of EL_3
target: el3-root-subgroups-are-bicommutant-closed
requires: []
artifacts:
  - research/artifacts/sk-rigidity-f2-2026-09-13.md
---

**(1).** `g ∈ GL_3(R)` centralizes `A_12` iff `g·rE_12 = rE_12·g` for every `r ∈ R`. Now `(g·rE_12)_{pq} = g_{p1} r`
when `q = 2` and `0` otherwise, and `(rE_12·g)_{pq} = r g_{2q}` when `p = 1` and `0` otherwise. Comparing entries
for all `r`:
- `(2,2)` and `(3,2)` give `g_21 r = g_31 r = 0`, so `g_21 = g_31 = 0` at `r = 1`;
- `(1,3)` gives `r g_23 = 0`, so `g_23 = 0`;
- `(1,2)` gives `g_11 r = r g_22`, so `g_11 = g_22 =: c` at `r = 1`, and then `c ∈ Z(R) = F_2`.

If `c = 0` the first column of `g` vanishes, contradicting invertibility, so `c = 1`. Every such `g` does centralize
`A_12`, by the same computation. Permuting indices gives
`C(A_13) = {g_11 = g_33 = 1, g_21 = g_31 = g_32 = 0}` and `C(A_32) = {g_22 = g_33 = 1, g_13 = g_23 = g_21 = 0}`.

**(2).** `A_12`, `A_13` and `A_32` satisfy the conditions of (1), so all three lie in `C_G(A_12)` and
`C_G(C_G(A_12)) ⊆ C_G(A_12) ∩ C_G(A_13) ∩ C_G(A_32)`. Intersecting the three displayed conditions leaves
`g_21 = g_31 = g_23 = g_32 = g_13 = 0` and `g_11 = g_22 = g_33 = 1`, that is `g = e_12(g_12) ∈ A_12`. The reverse
inclusion is trivial. The other five root subgroups follow by permuting indices, using that every permutation
matrix lies in `EL_3(R)`: over `F_2`, `e_12(1)e_21(1)e_12(1)` is the transposition matrix.

**(3).** `(E_12 b + E_13 c)(E_12 b' + E_13 c') = 0` because `E_1jE_1k = 0`, so `Row_1` is abelian; the same holds for
every `Row_i` and `Col_j`. By (1), `C_G(Row_1) = C_G(A_12) ∩ C_G(A_13)` is cut out by
`g_21 = g_31 = g_23 = g_32 = 0` and `g_11 = g_22 = g_33 = 1`, which is `Row_1`, and
`C_G(Col_2) = C_G(A_12) ∩ C_G(A_32)` is cut out by `g_21 = g_31 = g_23 = g_13 = 0` and `g_11 = g_22 = g_33 = 1`,
which is `Col_2`.

**(4).** An element of `Row_i` has its off-diagonal entries in row `i` and one of `Col_j` in column `j`, so the two
conditions leave only the `(i,j)` entry.

**The centre of `R_X`.** Let `c = Σ_j c_j u^j` be central. For clopen `V`,
`e_V c − c e_V = Σ_j c_j(e_V − e_{T^jV})u^j = 0`. If `x ∈ supp c_j` with `j ≠ 0` then `x ≠ T^{-j}x`, because a
minimal infinite subshift has no periodic points, so a clopen `V` containing `x` but not `T^{-j}x` forces
`c_j(x) = 0`, a contradiction. So `c = c_0 ∈ LC(X,F_2)`, and `ucu^{-1} = c` makes `c_0` `T`-invariant, hence
constant by minimality.
