---
rg: 2
id: sl3z-infinite-order-centralizers-are-solvable-proof
kind: route
title: Eigenvalue case analysis for centralizers in SL_3(Z)
target: sl3z-infinite-order-centralizers-are-solvable
requires: []
---

Let `p in Z[x]` be the characteristic polynomial of `g`: monic, cubic,
`p(0) = -det g = -1`. Every `h` commuting with `g` commutes with every
polynomial in `g`.

1. **Three distinct eigenvalues.** Then `g` is diagonalizable over `C` with
   distinct eigenvalues, and a matrix commuting with it is diagonal in the
   eigenbasis. So `C(g)` is abelian.
2. **A repeated eigenvalue `l`.** Then `l` is a root of `gcd(p, p')`, which
   lies in `Q[x]`.
   - If `l` has multiplicity 3, then `l = tr(g)/3` is rational and an
     algebraic integer, so `l in Z`, and `l^3 = det g = 1` gives `l = 1`:
     `g` is unipotent.
   - If `l` has multiplicity 2 and `m` is the simple root, then
     `gcd(p, p') = x - l`, so `l in Z`; `m = 1/l^2` is a rational algebraic
     integer, so `m in Z`, hence `l = ±1` and `m = 1`.
3. **`g` unipotent, `g != 1`** (infinite order excludes `g = 1`). Put
   `N = g - 1 != 0`.
   - If `N^2 != 0`, `N` is a regular nilpotent, whose centralizer in `M_3`
     is `{a + bN + cN^2}`: commutative. So `C(g)` is abelian.
   - If `N^2 = 0`, `N` has rank one, `N = v w^T` with `w^T v = 0`; in a
     rational basis starting with `v` and ending with a vector `e` with
     `w^T e = 1`, `N` is the matrix unit `E_13`. A matrix `M` commutes with
     `E_13` iff `M_21 = M_31 = M_32 = 0` and `M_11 = M_33` (compare the third
     column of `M E_13`, which is the first column of `M`, with the first row
     of `E_13 M`, which is the third row of `M`). So `C(g)` is conjugate into
     the upper triangular group, which is solvable.
4. **Eigenvalues `-1, -1, 1`.** Write the Jordan decomposition `g = su`,
   where `s` and `u` are polynomials in `g` with rational coefficients, `s`
   is semisimple with eigenvalues `-1, -1, 1` (so `s^2 = 1`) and `u` is
   unipotent. Infinite order forces `u != 1`. The eigenspaces
   `Q^3 = V_- + V_+` of `s` are rational, of dimensions 2 and 1, and
   `C(g) <= C(s) ∩ C(u)` with `C(s) <= GL(V_-) x GL(V_+)`. The unipotent `u`
   preserves both summands, is trivial on `V_+`, and so is a nontrivial
   unipotent `u_-` on `V_-`. The centralizer of `u_-` in `GL_2` is
   `{a + b(u_- - 1)}`: commutative. So `C(g)` is abelian.

In every case `C(g)` is solvable, and by Mal'cev it is polycyclic.
