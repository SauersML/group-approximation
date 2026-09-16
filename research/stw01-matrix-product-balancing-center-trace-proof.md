---
rg: 2
id: stw01-matrix-product-balancing-center-trace-proof
kind: route
title: Balance mean-zero diagonals by one permutation, so a quasitrace factors through the center-valued trace
target: stw01-matrix-product-algebras-have-qt-linearity
requires: []
artifacts:
  - research/artifacts/stw01-central-fiber-qt-linearity-2026-09-16.md
  - research/artifacts/stw01-certificates-products-universal-tests-2026-09-11.md
---

This route writes out in full the proof sketched as Proposition 5.2 of the
2026-09-11 certificates artifact, which carried no route.  The details are in §6 of
the 2026-09-16 artifact.  The argument uses only the axioms

- (i) `tau(x*x) = tau(xx*) >= 0`;
- (ii) `tau(a + ib) = tau(a) + i tau(b)` for self-adjoint `a, b`;
- (iii) `tau` is linear on every abelian C\*-subalgebra.

So it proves slightly more than the claim: on `W = prod_(i in I) M_(n_i)`, every
function `tau: W -> C` satisfying (i)-(iii) is a trace.  Neither boundedness nor the
`M_2` witness is used.

**Step 0: unitary invariance.**  Let `u` be unitary.

- For `y >= 0`, put `z = u y^(1/2)`.  Then `z*z = y` and `zz* = u y u*`, so (i) gives
  `tau(uyu*) = tau(y)`.
- For self-adjoint `y = y_+ - y_-`, both `y_+` and `y_-` lie in `C*(y)`.  Their
  conjugates `u y_+ u*` and `u y_- u*` are the positive and negative parts of
  `u y u*`, so they lie in `C*(uyu*)`.
- By (iii) on those two abelian algebras,
  `tau(uyu*) = tau(uy_+u*) - tau(uy_-u*) = tau(y_+) - tau(y_-) = tau(y)`.

**Step 1: balancing lemma.**  Let `c in R^n` with `sum_j c_j = 0` and `|c_j| <= M`.
We claim there are a real diagonal `w in M_n` with `||w|| <= M` and a permutation
unitary `v` with `diag(c) = w - v w v*`.

*Ordering.*  Choose the entries one at a time, keeping a running sum `s_k`, with
`s_0 = 0`.

- If `s_k <= 0`, pick a remaining entry `>= 0`.  One exists: if every remaining
  entry were negative and some remained, the total would be `< s_k <= 0`.
- If `s_k > 0`, pick a remaining entry `< 0`.  One exists by the symmetric argument.
- In the first case `s_(k+1) in [-M, M]`, since `s_k in [-M, 0]` and the entry lies
  in `[0, M]`.
- In the second case `s_(k+1) in (-M, M)`, since `s_k in (0, M]` and the entry lies
  in `[-M, 0)`.

Let `rho` record the order, so the `j`-th chosen entry is `c_(rho(j))`.  Put
`w_j = s_j` for `0 <= j <= n`.  Then `w_0 = w_n = 0`, `|w_j| <= M`, and
`c_(rho(j)) = w_j - w_(j-1)`.

*Matrices.*

- Let `S e_j = e_(j+1)`, with indices mod `n`, and `D_w = diag(w_1, ..., w_n)`.
- Then `S D_w S* = diag(w_n, w_1, ..., w_(n-1)) = diag(w_0, ..., w_(n-1))`.
  Hence `D_w - S D_w S* = diag(c_(rho(1)), ..., c_(rho(n)))`.
- Let `P e_j = e_(rho(j))`.  Then `P diag(a_1, ..., a_n) P*` has entry `a_j` at
  position `rho(j)`, so `P (D_w - S D_w S*) P* = diag(c)`.
- Put `w = P D_w P*` and `v = P S P*`.  Then `v w v* = P S D_w S* P*`, so
  `diag(c) = w - v w v*`, with `w` real diagonal, `||w|| <= M` and `v` a permutation
  unitary.

**Step 2: diagonal elements.**  Let `D = prod_i D_(n_i)` be the diagonal
subalgebra, which is abelian.  Let `T(x) = (tr_(n_i)(x_i) 1_(n_i))_i`, with `tr`
normalized.  `T` is linear, `T(uxu*) = T(x)` for unitaries `u in W`, and
`T(W) = Z(W) subset D`.

Let `d in D_sa` and `c = d - T(d)`.

- In each block, `c_i` is real diagonal with trace `0` and entries bounded by
  `2||d||`.
- Step 1 in each block gives `w_i` and `v_i` with `||w_i|| <= 2||d||`.  So
  `w = (w_i) in D` and `v = (v_i)` is a unitary of `W`.
- `v w v*` is again diagonal, so `d = T(d) + w - v w v*` is a sum of elements of `D`.

By (iii) on `D` and Step 0,
`tau(d) = tau(T(d)) + tau(w) - tau(vwv*) = tau(T(d))`.

**Step 3: self-adjoint elements.**  For `x in W_sa`, diagonalize each block:
`x_i = u_i d_i u_i*`.  Here `u = (u_i)` is a unitary of `W` and `d = (d_i) in D_sa`,
with `||d_i|| = ||x_i||`.  Steps 0 and 2 give

```text
tau(x) = tau(d) = tau(T(d)) = tau(T(x)).
```

**Step 4: linearity and traciality.**  For `x, y in W_sa` and real `t`, the elements
`T(x)`, `T(y)`, `T(x + y)` and `T(tx)` lie in the abelian algebra `Z(W)`.  By (iii)
and Step 3,

```text
tau(x + y) = tau(T(x) + T(y)) = tau(x) + tau(y),
tau(tx)    = t tau(x).
```

For a general `z = a + ib` and `lambda = l_1 + i l_2`, (ii) gives

```text
tau(lambda z) = tau(l_1 a - l_2 b) + i tau(l_2 a + l_1 b) = lambda tau(z),
```

and additivity in `z` follows from additivity on `W_sa`.  So `tau` is a linear
functional.  It is positive by (i).  Polarizing `tau(x*x) = tau(xx*)` gives
`tau(y*x) = tau(xy*)` for all `x, y`, hence `tau(xy) = tau(yx)`.  So `tau` is a
trace.

**Step 5: quotients.**  Let `J` be a closed ideal, `q: W -> W/J` the quotient map,
and `sigma` a bounded 2-quasitrace on `W/J`.

- `sigma o q` satisfies (i) and (ii), since `q` is a star homomorphism.
- It satisfies (iii): `q` maps an abelian C\*-subalgebra onto an abelian
  C\*-subalgebra, on which `sigma` is linear.

By Steps 0-4, `sigma o q` is linear.  Since `q` is onto, `sigma` is linear, hence a
trace as in Step 4.  Norm ultraproducts `prod_omega M_(n_k)` are the quotients by
`{x : lim_omega ||x_k|| = 0}`, so they are included.  QED.

**Remark on the parenthetical non-exactness in the claim.**  This is not part of
the linearity assertion.  The standard argument uses three facts that were not
re-read this session:

- `C*(F_2)` is residually finite dimensional (Choi, 1980).
- `C*(F_2)` is not exact (Wassermann, 1976).
- Exactness passes to C\*-subalgebras (Kirchberg).

A separable RFD algebra has finite-dimensional representations `pi_j`, taken as
cumulative direct sums, with `||pi_j(a)||` increasing to `||a||`.  If `n_k -> infinity`,
the maps `a -> pi_(j(k))(a) (+) 0` embed it isometrically into `prod_omega M_(n_k)`.
Here `j(k)` is the largest `j <= k` with `dim pi_j <= n_k`.
