# Two transcendental coefficients under the determinant conjecture, part 3

Lane `ex2-atiyah-base-change-td2`, 2026-09-13. Continues Parts 1-2. This part
builds a form `F` that violates (CYC) and so proves Theorem 5. **Unreviewed.**

Put `B = N / kappa_0 >= 1`. Then (CYC) reads
`a(F) + (B - 1) b(F) + C_3 deg F >= 0`, with `C_3 = C_2 / kappa_0`. Fix

```text
n = ceil(100 B^2),     n_2 = 4 B n + 1  (rounded up to an integer),     gamma = 5 B.
```

`c_4, c_5, ...` denote constants depending only on `n`, `n_2`, `z`, `M`, `Y`
and a shear parameter `t in {0, ..., n}`. The heights `H_1`, `H_2` are free.

## 5. The construction

**Step 1 (one small bivariate polynomial).** Let `m = (n+1)(n+2)/2` and
`w = m/2 - 1 >= n^2/4`. By the complex box principle (Section 5 of the
one-variable artifact, with `m` coefficients), for every `H >= 1` there is a
nonzero `p in Z[x_1, x_2]` with `deg p <= n`, `H(p) <= H` and
`|p(z)| <= c_4 H^-w`.

**Step 2 (an irreducible factor with the same exponent).**
* **Factor.** Write `p = ± prod_i p_i^(e_i)` with `p_i` primitive irreducible.
  Via Mahler measure, `prod_i H(p_i)^(e_i) <= e^(c_6) H`.
* **Small factors.** For `T >= 1` let `delta(T)` be the least `|P(z)|` over
  nonzero `P` with `deg P <= n` and `H(P) <= T`. It is positive, because `z_1`
  and `z_2` are algebraically independent. The factors with `H(p_i) <= T`
  contribute at least `n log delta(T)` to `log |p(z)|`.
* **Mediant.** So the factors with `H(p_i) > T` satisfy
  `sum e_i log |p_i(z)| <= log c_4 - w log H - n log delta(T)` and
  `sum e_i log H(p_i) <= log H + c_6`. Some such factor `p_1` therefore has

  ```text
  -log |p_1(z)|  >=  w_H log H(p_1),        w_H = (w log H - log c_4 + n log delta(T)) / (log H + c_6),
  ```

  with `H(p_1) > T`. For fixed `T`, `w_H -> w` as `H -> infinity`. Choose `T`,
  then `H`, so that `w_H >= n^2/8` and `log H(p_1) >= log T`, where `T` is as
  large as needed below.

**Step 3 (make the leading coefficient in `x_2` constant).**
* **Swap.** If `p_1 in Z[x_1]`, swap the coordinates throughout (of `z`, `M`
  and `Y`).
* **Shear.** Otherwise let `P_top` be the top-degree form of `p_1`, of degree
  `d`, and choose `t in {0..d}` with `P_top(t, 1) != 0`. Replace `p_1(x)` by
  `p_1(x_1 + t x_2, x_2)`, `M(x)` by `M(x_1 + t x_2, x_2)`, `z` by
  `(z_1 - t z_2, z_2)`, and `Y` by its preimage.
* **What is preserved.** Integrality, fullness, `kappa_0`, algebraic
  independence and the value `p_1(z)` are unchanged. Heights change by at most
  `e^(c n)`. Now `p_1` is irreducible of degree `d <= n`, and its coefficient of
  `x_2^d` is a nonzero integer `c_1`.
* **Constants.** Parts 1-2 apply to the sheared data. Take `C_3` as the maximum
  over the finitely many `t` and the two orderings.

Put `L_1 = log H(p_1)` and `g_1 = -log |p_1(z)| >= (n^2/8) L_1 - c_7`.

**Step 4 (one small one-variable polynomial).** Put
`H_2 = ceil(exp(gamma L_1))` and `L_2 = log H_2 in [gamma L_1, gamma L_1 + 1]`.
By the one-variable complex box principle there is a nonzero `q in Z[x_1]` with
`deg q = n_2' <= n_2`, `H(q) <= H_2` and
`|q(z_1)| <= c_8 H_2^(-w_2)`, `w_2 = (n_2 - 1)/2 = 2 B n`.

**Step 5 (the form).** Put

```text
R(x_1, u) = u_2^d p_1(x_1, -(u_0 + u_1 x_1)/u_2)  in Z[x_1, u],
F(u)      = Res_(x_1)(q, R(., u)),  with formal degrees (n_2', d).
```

* **Why `R` is a polynomial.** A monomial `x_1^i x_2^j` with `i + j <= d`
  becomes `x_1^i (-(u_0 + u_1 x_1))^j u_2^(d-j)`. So `R` is a polynomial of
  degree `<= d` in `x_1`.
* **Factorization of `R`.** For `alpha in C`,
  `p_1(alpha, y) = c_1 prod_(k=1..d) (y - beta_k(alpha))`, so
  `R(alpha, u) = ± c_1 prod_k (u . (1, alpha, beta_k(alpha)))`.
* **Factorization of `F`.** By Poisson's formula,
  `F = ± a_q^d c_1^(n_2') prod_(q(alpha) = 0) prod_k u . (1, alpha, beta_k(alpha))`,
  where `a_q` is the leading coefficient of `q`.
  - `F` is integral, of degree `d n_2' <= n n_2`, and a product of linear forms
    at affine points.
  - `F` is nonzero, because every factor is.
  - `p_1 notin Q[x_1]` is irreducible, so `p_1(alpha, .)` never vanishes
    identically. No coprimality condition on `q` is needed.

**Step 6 (sizes, by Hadamard).** The Sylvester matrix `S(u)` has `d` rows of
coefficients of `q` (entries `<= H_2`) and `n_2'` rows of coefficients of `R`
in `x_1`. For `|u_i| <= 2 R'`, where `R' = max(1, |z_1|, |z_2|)`, the latter
entries are `<= m 2^d (2R')^d H_1`.
* **`b`.** By (M4) and Hadamard, `b(F) <= d L_2 + n_2' L_1 + c_9`.
* **`a`.** Replace the last column of `S` by
  `(x_1^(d-1) q, ..., q, x_1^(n_2'-1) R, ..., R)^T`. Expanding gives the
  identity `F = A(x_1, u) q(x_1) + B(x_1, u) R(x_1, u)` in `Z[u][x_1]`.
  - The coefficients of `A` are minors missing one `q`-row, of size
    `<= c H_2^(d-1) H_1^(n_2')`. Those of `B` miss one `R`-row, of size
    `<= c H_2^d H_1^(n_2' - 1)`.
  - For `v in T^3` put `u = theta~ x v`. Then `u . theta~ = 0` and
    `|u_i| <= 2R'`. So `-(u_0 + u_1 z_1)/u_2 = z_2`, and
    `R(z_1, u) = u_2^d p_1(z)`, by continuity also where `u_2 = 0`.
  - Evaluating the identity at `x_1 = z_1` and using (M4):

  ```text
  a(F)  <=  c_10 + max( (d-1) L_2 + n_2' L_1 - w_2 L_2 ,  d L_2 + (n_2' - 1) L_1 - g_1 ).
  ```

**Step 7 (the contradiction).** Use `d <= n`, `n_2' <= n_2` and `L_i >= 0`.
Then

```text
a(F) + (B-1) b(F)  <=  c_11 + max( (B n - w_2) L_2 + B n_2 L_1 ,  B n L_2 + B n_2 L_1 - g_1 ).
```

* **First branch.** `w_2 = 2Bn` and `L_2 >= 5B L_1`, so it is at most
  `-5B^2 n L_1 + (4B^2 n + 2B) L_1 <= -L_1`.
* **Second branch.** `L_2 <= 5B L_1 + 1` and `g_1 >= (n^2/8) L_1 - c_7`, so it
  is at most `(9 B^2 n + 2B - n^2/8) L_1 + c_12 <= -L_1 + c_12`, since
  `n >= 100 B^2`.

Hence `a(F) + (B-1) b(F) + C_3 deg F <= c_13 - L_1`, with `c_13` independent of
`T`. Choosing `T > e^(c_13)` makes this negative, which contradicts (CYC). So
`kappa_0 = 0`, and Theorem 5 is proved. ∎

## 6. Remarks, scope, model tests

* **Why this beats the earlier attempts.**
  - The Kronecker product of companion pencils uses two one-variable
    polynomials. Their exponents `n_i/2` are too weak, and neither branch closes.
  - Here the bivariate factor has exponent about `n^2/4` against a loss of
    order `n_2 ~ 4Bn`.
  - Transversality never enters. `q` depends on `x_1` alone and `p_1` is
    irreducible with constant leading coefficient in `x_2`, so the cycle
    `V(p_1, q)` is automatically zero-dimensional.
  - The iterated-resultant attempt bounded determinants one coordinate at a
    time. Here the determinant conjecture is applied once, to the cycle model
    (RES2).
* **Model test, `G = 1`.** Then `det M(x) = P(x) in Z[x]`, and Proposition C
  says `log |N_(K/Q) P(zeta)| + deg P h_fin(Z) >= 0`. This is the product
  formula plus the ultrametric bound `|P(zeta)|_w <= pi_w^(deg P)`, so the
  determinant conjecture enters exactly as integrality does.
* **Model test, a rational point.** For `Z = {(1/2, 1/3)}` we get
  `Lambda_k = 6^-k Z`, index `6`, and Chow form `6u_0 + 3u_1 + 2u_2`, so
  `h_fin = log 6 = log |c_Z|`.
* **Hypotheses used.** Strong Atiyah over `Qbar` enters only in Lemma J and
  Lemma L. The determinant conjecture enters only in Proposition C. Lueck's
  (D1)-(D3) are imported as in the one-variable artifact, not re-read.
* **What is not proved here.**
  - Transcendence degree `>= 3`. The Part 2 machinery works in `A^s` verbatim.
    The missing input is a form in `s` variables with
    `a(F) + (B-1) b(F) + C deg F < 0`.
  - The naive triangular chain `V(q(x_1), p_2(x_1,x_2), p_3(x_1,x_2,x_3))`
    fails. Its degrees force `n_1 >> n_2 n_3`, `n_2^2 >> n_1 n_3` and
    `n_3^3 >> n_1 n_2`, which are incompatible.
  - Algebraic extensions of `Qbar(z_1, z_2)` should follow as in Theorem 4:
    fibre sums are constant off `Y`, then continuity and connectedness. This
    is not yet written out.
* **Novelty check (bounded).** The web-search budget was exhausted in this
  session. Jaikin-Zapirain's base change for sofic groups (GAFA 2019) goes
  through approximation, and this argument uses none. No source was found for
  Proposition C or for Step 5 in this context. A literature check is still
  owed.
