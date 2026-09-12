---
rg: 2
id: galois-invariance-base-change-proof
kind: route
title: Induct on transcendence degree with a central variable and two coprime restrictions of scalars
target: strong-atiyah-base-change-from-galois-invariance
requires: []
---

Write `x(A) = dim_(N(H)) ker r_A`.  Complex conjugation is not assumed to
commute with `sigma`.

**Induction.**  For `k >= 0` let `S(k)` say: every `G x Z^j` satisfies Strong
Atiyah over every algebraically closed subfield `L` of `C` with
`trdeg_Q L <= k`.  `S(0)` is hypothesis 1 (the only such `L` is `Qbar`).  Every
matrix over `C[G]` has coefficients in the algebraic closure of a finitely
generated field, so it suffices to derive `S(k)` from `S(k-1)`.

Fix `H = G x Z^j` and an algebraically closed `L'` of transcendence degree `k`.
Choose a transcendence basis `t_1..t_k` of `L'` and let `L` be the algebraic
closure of `Qbar(t_1..t_(k-1))`; then `L <= L'`, `L` is countable, and `L'` is
algebraic over `L(t_k)`.  Let `A` be over `L'[H]` with coefficient set `a`.  If
`a <= L`, apply `S(k-1)`.  Otherwise `F = L(a)` has transcendence degree 1 over
the algebraically closed field `L`, so it is the function field of a smooth
projective curve of genus `g` over `L`.

**Step 1: two coprime degrees.**  Fix a point `P` and put `n = max(2g,1)`.
Riemann--Roch gives `l(mP) = m+1-g` for `m >= 2g-1`, so for `m = n, n+1` there
is `f_m in F` with pole divisor exactly `mP`.  Then `[F : L(f_m)] = m`.

**Step 2: restriction of scalars.**  Fix `f = f_m`, `d = m`, a basis `w` of `F`
over `L(f)`, the regular representation `rho: F -> M_d(L(f))`, and the `d`
distinct embeddings `sigma_s: F -> C` over `L(f)`, with `sigma_1` the
inclusion.  The complex matrix `P = (sigma_s(w_t))` is invertible and
`P rho(y) P^(-1) = diag_s sigma_s(y)`.  So `rho(A)`, over `L(f)[H]`, is
conjugate by invertible scalar matrices to the direct sum of the `sigma_s(A)`.
Each `sigma_s` extends to an automorphism of `C` fixing `Qbar`, so
hypothesis 2 gives

```text
x(rho(A)) = sum_s x(sigma_s(A)) = d x(A).
```

Multiply by a common denominator `q(f)`, a nonzero complex scalar because `f`
is transcendental over `L`.  This gives `B(f)` over `L[f][H]` with
`x(B(f)) = d x(A)`.

**Step 3: central variable.**  Replace `f` by a central generator `z` of a new
factor `Z`, giving `Btilde` over `L[H x Z]`.  For `zeta` in the unit circle `T`,
`z -> zeta` is a star homomorphism `C[H x Z] -> C[H]` (`z* = z^(-1)`), and
`integral_T zeta^p dzeta = delta_(p,0)`.  So every moment of the spectral measure
of `Btilde* Btilde` is the Haar average over `zeta` of the moments for
`B(zeta)* B(zeta)`.  The measures are uniformly supported, so the first is the
average of the others, and

```text
x(Btilde) = integral_T x(B(zeta)) dzeta.
```

**Step 4: invariance on generic points.**  All but countably many `zeta in T`
are transcendental over the countable field `L`.  For such `zeta`,
`f -> zeta` is an isomorphism `L(f) -> L(zeta)` over `L`; it extends to an
automorphism `sigma` of `C` with `sigma(B(f)) = B(zeta)`.  Hypothesis 2 gives
`x(B(zeta)) = x(B(f))` almost everywhere, so `x(Btilde) = d x(A)`.  By `S(k-1)`
for `H x Z = G x Z^(j+1)` over `L`, this is an integer.

**Conclusion.**  `n x(A)` and `(n+1) x(A)` are integers, so `x(A)` is.  This
proves `S(k)`.  QED
