---
rg: 2
id: kt-polynomial-subgroup-icc-proof
kind: route
title: A finite-index centralizer forces the substitution to fix a finite-codimension subspace, hence to be trivial, and the matrix part to be scalar
target: kt-polynomial-subgroup-is-icc-in-kt-group
requires: []
---

Write `R = F_2[x^(+-1)]`, `R_+ = F_2[x_1..x_d]`, and elements of `G` as `(m,A)`
with `m in EL_r(R)` and `A in SL_d(Z)` acting on `R` by the monomial
automorphism `x^a -> x^(Aa)`, so `(m,A)(n,B) = (m A(n), AB)`. By
orbit--stabilizer it suffices to show: if `C_Gamma(h)` has finite index in
`Gamma`, then `h = e`.

**Step 1 (root coordinates).** For `i != j` put `U_ij = {e_ij(p) : p in R_+} <= Gamma`.
`U_ij cap C_Gamma(h)` has finite index in `U_ij ~= (R_+, +)`. So
`Q_ij = {p : [e_ij(p), h] = 1}` is an `F_2`-subspace of finite codimension in
`R_+`.

**Step 2 (commutation equation).** For `h = (m,A)`,
`h (e_ij(p), I) h^(-1) = (m e_ij(A(p)) m^(-1), I)`. So `p in Q_ij` iff

```text
A(p) X = p E_ij,        X = m E_ij m^(-1).
```

For nonzero `p in Q_ij`, `A(p) != 0`, so `X = (p / A(p)) E_ij` over `Frac R`.
Comparing `(i,j)` entries, `A(p) = mu p` for all `p in Q_ij`, with one
`mu in (Frac R)^x`.

**Step 3 (`A` fixes a finite-codimension subspace).** Fix `p_0 in Q_ij - {0}` and let
`K = {y in R_+ : y p_0 in Q_ij}`, the kernel of `y -> y p_0 mod Q_ij` into a
finite-dimensional space. So `K` has finite codimension in `R_+`. For `y in K`,
`A(y) A(p_0) = A(y p_0) = mu y p_0 = y A(p_0)`, so `A(y) = y`.

**Step 4 (`A = I`).** `A` permutes the monomial basis `{x^a : a in Z^d}` of `R`.
A fixed element has finite `A`-invariant support with coefficients constant
along `A`-orbits. Let `T = {a in N^d : Aa != a}`. For `f in R_+` fixed by `A` and
`a in T`, the coefficient of `x^a` equals that of `x^(Aa)` (zero if
`Aa notin N^d`). Choose infinitely many `a in T` whose pairs `{a, Aa}` are pairwise
disjoint; this is possible when `T` is infinite, since each `a` meets at most
the two points `Aa, A^(-1)a`. The functionals `f -> coef_a(f) - coef_(Aa)(f)` then
have disjoint supports, so they are linearly independent, and they all vanish
on the fixed subspace. So if `T` were infinite, the fixed subspace of `R_+` would
have infinite codimension, contradicting Step 3. Hence `T` is finite, so `A`
fixes `N e_k` for all large `N` and every `k`, and `A = I`.

**Step 5 (`m = I`).** With `A = I`, Step 2 gives `mu = 1` and
`m E_ij m^(-1) = E_ij` for every `i != j`. The `E_ij` (`i != j`) generate `M_r`
(`E_ii = E_ij E_ji`), so `m = lambda I` with `lambda in R^x`. Since
`m in EL_r(R) <= SL_r(R)`, `lambda^r = 1`. The units of `F_2[x^(+-1)]` are the
monomials `x^a`, so `a = 0` and `m = I`. Hence `h = e`.

**Conjugates.** `C_(t Gamma t^(-1))(h) = t C_Gamma(t^(-1) h t) t^(-1)`, so the
conclusion transfers to every `G`-conjugate of `Gamma`.
