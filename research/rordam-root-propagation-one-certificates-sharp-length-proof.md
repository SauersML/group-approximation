---
rg: 2
id: rordam-root-propagation-one-certificates-sharp-length-proof
kind: route
title: Descend a one-shift certificate to stage one, read it as a rank-two section, and evaluate the Porteous class by Schur positivity
target: rordam-root-propagation-one-certificates-sharp-length
requires: []
artifacts:
  - experiments/rordam-one-shift-certificates-2026-09-17/porteous_class.py
  - experiments/rordam-one-shift-certificates-2026-09-17/porteous_class.out
---

Notation is that of Rørdam, Acta Math. 191 (2003), arXiv:math/0204339v2, Sections 4–6.
- `Z = prod_{i>=1} S^2`, `A = C(Z) (x) K`, and `M(A)` is its multiplier algebra.
- `phi_j`, `alpha_j`, `phi = sum_j T^* S_j phi_j(.) S_j^* T` and its unital extension to `M(A)` are as in (5.3)–(5.6).
- `B = lim (M(A), phi)` with maps `mu_n = mu_{infty,n}`. The automorphism `alpha` satisfies `alpha(mu_n(x)) = mu_n(phi(x))` and
  `alpha^{-1}(mu_n(x)) = mu_{n+1}(x)`.
- `A_0 = mu_0(A)`, `A_k = alpha^k(A_0)`, and `D = closure of union D_n`, where `D_n = C^*(A_{-n}, ..., A_n)`.
- We fix the unitary `u` in `D x_alpha Z` with `u d u^* = alpha(d)`.

For a finite `J` in `N`, `p_J` is the product of the Bott projections in the coordinates of `J` ((4.2)). It is a rank-one
projection whose line bundle `zeta_J` has first Chern class `x_J = sum_{i in J} x_i`, where
`H^*((S^2)^k) = Z[x_1, ..., x_k]/(x_i^2)` ((4.9) and Prop. 3.2). Put `e_J = mu_0(p_J)`.

**Definitions.**
- `J` is *row-free* if `J` and `alpha_j(J)` are disjoint for every `j` in `Z`.
- A *one-shift certificate of length N and slack delta* for `e_J` consists of elements `x_1, ..., x_N` of the form
  `x_s = c_s u^*` with `c_s in D` and `x_s in e_J (D x_alpha Z) e_J`, such that
  `||sum_s x_s^* x_s - e_J|| < eps` and `||sum_s x_s x_s^*|| <= 1 - delta`.
- `nu_1(e_J)` is the least `N` for which such certificates exist for every `eps > 0` and some `delta > 0`.

Exact certificates with `sum x^* x = e_J` and `||sum x x^*|| <= 1/2`, as in Milhøj–Rørdam Remark 4.7, are a special case.

## Step 0. Monomialization of arbitrary certificates

Let `E : D x_alpha Z -> D` be the canonical conditional expectation. Suppose `x_1, ..., x_N` lie in the algebraic crossed
product, with `x_s = sum_{|n| <= L} d_{s,n} u^n`. Then:
- `E(x_s^* x_s) = sum_n alpha^{-n}(d_{s,n}^* d_{s,n})` and `E(x_s x_s^*) = sum_n d_{s,n} d_{s,n}^*`, since `E(u^k) = 0`
  for `k != 0`.
- `E` is positive, unital on the corner and contractive, and `E(e_J) = e_J`.

So if `{x_s}` satisfies `||sum x^* x - e_J|| < eps` and `||sum x x^*|| <= 1 - delta`, the monomials `y_{s,n} = d_{s,n} u^n`
satisfy the same two inequalities. Each `y_{s,n}` again lies in the corner, because `d_{s,n} = e_J d_{s,n} alpha^n(e_J)`
after compressing `x_s` by `e_J` on both sides.

Hence every certificate of finite propagation `L` and length `N` yields a *monomial* certificate of length
`N(2L+1)`. This theorem settles the part where all monomials have shift `-1`. (Shift `+1` and mixed shifts are discussed
in the target's scope paragraph.)

## Step 1. Where the coefficients of a one-shift monomial live

Let `x = c u^*` lie in `e_J (D x Z) e_J`. Then `x = e_J x e_J` gives `c = e_J c alpha^{-1}(e_J)`, where
`alpha^{-1}(e_J) = mu_1(p_J)`, which lies in `A_{-1}`.

By Rørdam (6.6) and (6.8):
- `A_k A_l <= A_{min(k,l)}`, and `D_{m,n} = A_m + ... + A_n` is closed.
- A word in `A_{-n}, ..., A_n` followed by an element of `A_{-1}` lies in `A_{k}` for some `k <= -1`.

So `c alpha^{-1}(e_J)` lies in the closure of `D_{-n,-1} = A_{-n} + ... + A_{-1}` for `c in D_n`, and by density, for
`c in D` up to arbitrarily small error. Since `A_{-k} = mu_k(A) = mu_n(phi^{n-k}(A))`,

```
D_{-n,-1} = mu_n( X_n ),   X_n := A + phi(A) + ... + phi^{n-1}(A)   (a C*-subalgebra of M(A)).
```

The algebra `X_n` is closed: `A` is an ideal in `M(A)`, and inductively `X_n = A + phi(X_{n-1})`. The same identities give
`e_J = mu_n(phi^n(p_J))` and `alpha^{-1}(e_J) = mu_n(phi^{n-1}(p_J))`.

**Conclusion of Step 1.** Up to `eps`, a one-shift certificate of length `N` is given by `n >= 1` and elements
`z_1, ..., z_N` of `phi^n(p_J) X_n phi^{n-1}(p_J)` satisfying:
- `||sum_s z_s^* z_s - phi^{n-1}(p_J)|| < eps'`;
- `||sum_s z_s z_s^*|| <= 1 - delta'`.

Here `x_s^* x_s = alpha(c_s^* c_s)` and `x_s x_s^* = c_s c_s^*`, `alpha` is isometric, and `mu_n` is injective because `phi`
is injective (Prop. 5.2(ii)).

## Step 2. Descent to stage one

**Claim.** If `n >= 2` and `z_s` as above exist, then elements `z'_s` of `phi^{n-1}(p_J) X_{n-1} phi^{n-2}(p_J)` exist with
the same `N`, `eps'` and `delta'`.

*Proof.*
- Let `q : X_{n+1} -> X_{n+1} / A` be the quotient map. `X_{n+1}` contains `X_n` and `phi^n(p_J)`, and `X_n` is a
  bimodule over `phi^n(A)`, since `phi^n(A) phi^k(A) <= phi^k(A)` for `k < n`.
- Since `X_{n+1} = A + phi(X_n)`, `X_n = A + phi(X_{n-1})` and `phi(M(A))` meets `A` only in 0 (Prop. 5.2(ii)), `q` restricted to `phi(X_{n-1})`
  is an injective *-homomorphism, hence isometric, and `q(X_n) = q(phi(X_{n-1}))`.
- Define `z'_s` by `q(z_s) = q(phi(z'_s))`. Because `phi` is injective, `z'_s` lies in the corner
  `phi^{n-1}(p_J) X_{n-1} phi^{n-2}(p_J)`.
- The certificate inequalities pass through `q`, since `q` is contractive and
  `q(phi^{n-1}(p_J)) = q(phi(phi^{n-2}(p_J)))`. They then pull back through the isometry `q o phi`.

Iterating the claim reaches `n = 1`, where `X_1 = A`. **Every one-shift certificate of length `N` yields `c_1, ..., c_N`
in `phi(p_J) A p_J` with `||sum c_s^* c_s - p_J|| < eps'` and `||sum c_s c_s^*|| <= 1 - delta'`.** Conversely, such
`c_s` give the one-shift certificate `x_s = mu_1(c_s) u^*`. Step 1 run backwards makes this exact: with `eps' = 0`,
`sum x^* x = alpha(mu_1(sum c^* c)) = alpha(mu_1(p_J)) = e_J`.

## Step 3. Truncation and the fibre picture

- Put `f_F = sum_{j in F} T^* S_j phi_j(p_J) S_j^* T` for finite `F` in `Z`. Then `f_F` increases strictly to `phi(p_J)`.
- Since `c_s = c_s p_J` lies in `A`, we have `||(phi(p_J) - f_F) c_s|| -> 0`.
- Compression by `f_F` does not increase `||sum c c^*||`. After shrinking `eps'` and `delta'` slightly, we may therefore
  assume `c_s in f_F A p_J` for a finite `F` with `|F| = r`.
- By Lemma 5.4, `phi_j(p_J) ~ p_{alpha_j(J)}`, and `S_j`, `T` are isometries. So `f_F A p_J` is the space of continuous
  sections of `Hom(zeta_J, E)`, where `E = (+)_{j in F} zeta_{alpha_j(J)}`.
- Sets `alpha_j(J)` for distinct `j` are disjoint, since they lie in distinct rows `nu({j} x N)`. Each has at least
  `m = |J|` elements: `|alpha_j(J)| = |nu(j, J u {1..j})| >= m`.
- By norm approximation, the sections may be taken to depend only on the finitely many coordinates in `J u (union of
  alpha_j(J), j in F)`. Call their number `k`.

A tuple `(c_1, ..., c_N)` is a section of `H = Hom(C^N, E')`, where `E' = zeta_J^* (x) E` has rank `r`. At a point `x` let
`M(x)` be the resulting `r x N` matrix. Then:
- `sum_s c_s^* c_s (x) = ||M(x)||_HS^2`, a scalar on the line `zeta_J`;
- `sum_s c_s c_s^* (x) = M(x) M(x)^*`, with norm `sigma_1(M(x))^2`.

So the inequalities read `||M||_HS^2 > 1 - eps'` and `sigma_1^2 <= 1 - delta'`. For `eps' < delta'` this forces
`sum_{i >= 2} sigma_i^2 > 0`, that is, **`rank M(x) >= 2` at every point.**

Conversely, let `M` be a section with rank at least 2 everywhere. Put `M~ = M h(M^* M)` with
`h(t) = min(1, sigma_2(M) / sqrt(t))`, which is continuous where `sigma_2 > 0`. This caps every singular value at
`sigma_2`, so at least two singular values of `M~` equal the top one. Hence `M~ / ||M~||_HS` has HS norm 1 and
`sigma_1^2 <= 1/2`. **So exact certificates of length `N` with constant 1/2 exist iff some finite `F` admits a section
of `Hom(C^N, E'_F)` of rank at least 2 everywhere.**

## Step 4. Lower bound: no certificate of length N <= m+1 (J row-free)

Let `Sigma_1` be the locus of maps of rank at most 1 in `Hom(C^N, C^r)`. It is a closed, irreducible,
`GL_r`-invariant affine cone of complex codimension `c = (N-1)(r-1)`.

**Thom–Porteous.** See Fulton, *Intersection Theory*, Thm. 14.4, and the equivariant form in Fehér–Rimányi. For a
rank-`r` bundle `E'` over a finite CW complex `Y` and `H = Hom(C^N, E')`, the fundamental class of `Sigma_1(H)` lies in
`H^{2c}(H, H \ Sigma_1(H))`. Its image in `H^{2c}(H) = H^{2c}(Y)` is

```
Delta(E') = det[ c_{r-1+j-i}(E') ]_{1 <= i,j <= N-1}.
```

Suppose a section `s` of `H` misses `Sigma_1(H)`. Then `s^* Delta(E')` factors through the composite
`H^{2c}(H, H \ Sigma_1) -> H^{2c}(H) -> H^{2c}(H \ Sigma_1)`, which is zero. So `Delta(E') = 0`. (For `r = 1` we have
`c = 0` and `Delta = 1`, and the conclusion is trivial.)

**Evaluation.**
- The Chern roots of `E'` are `w_K = x_K - x_J` for `K = alpha_j(J)`, `j in F`.
- By the dual Jacobi–Trudi identity, `det[e_{mu_i + j - i}] = s_{mu'}`. With `mu = (r-1)^{N-1}` this gives
  `Delta(E') = s_lambda(w_K : K)`, where `lambda = (N-1)^{r-1}`.
- Restrict to the slice `Y_0` on which every coordinate in `J` is frozen. Because `J` is row-free, `x_J` restricts to 0
  and each `x_K` is unchanged. So `Delta(E')|_{Y_0} = s_lambda(x_{K_1}, ..., x_{K_r})`.
- Expand `s_lambda = sum_mu K_{lambda,mu} m_mu` with Kostka numbers `K_{lambda,mu} >= 0` and `K_{lambda,lambda} = 1`.
- In `Z[x_i]/(x_i^2)` we have `x_K^a = a! e_a(x_i : i in K)`. This is nonzero iff `a <= |K|`.
- The blocks `K` are disjoint. So the products `prod_K x_K^{a_K}` for distinct exponent vectors `a` have distinct block
  multidegrees and are linearly independent.
- Hence `Delta|_{Y_0}` is a nonnegative combination of independent nonzero elements. It contains `x^lambda` with
  coefficient at least 1 as soon as `N - 1 <= min_K |K|`, and `min_K |K| >= m`.

**So for `N <= m+1` we get `Delta(E') != 0` for every finite `F`.** By Step 3 no one-shift certificate of length `N`
exists, for any slack `delta > 0` and any `eps < delta`.

## Step 5. Upper bound: certificates of length m+2 exist

Take `N = m+2` and `r = 2m+2`. Choose `F` among the indices `j <= 0`, so that `alpha_j(J) = nu(j, J)` has size `m` and is
disjoint from `J` and from the other chosen sets. The sections involve `k = m + rm = m(2m+3)` coordinates.

The real codimension of `Sigma_1(H)` is `2(N-1)(r-1) = 4m^2 + 6m + 2`, which exceeds `dim (S^2)^k = 4m^2 + 6m`.

Existence follows by either of two arguments.
- *Transversality.* `Sigma_1(H)` is a locally trivial subbundle whose fibre is stratified by rank into smooth strata of
  real codimension at least `2(N-1)(r-1)`. A smooth section transverse to every stratum exists (parametric
  transversality), and it misses all of them for dimension reasons.
- *Obstruction theory.* The fibre `C^{Nr} \ Sigma_1` is `(2c-2)`-connected. Since `2k <= 2c-1`, a section over the
  `2k`-dimensional base exists.

Pull the section back to `Z` along the coordinate projection. Step 3 (converse) turns it into exact `c_s` with
`sum c_s^* c_s = p_J` and `||sum c_s c_s^*|| <= 1/2`. Step 2 (converse) gives `x_s = mu_1(c_s) u^*` with
`sum x_s^* x_s = e_J` and `||sum x_s x_s^*|| <= 1/2`. So `nu(e_J (D x Z) e_J) <= m+2`.

## Step 6. Row-free sets exist in every size

If `nu(j, a)` lies in `J`, say it equals `nu(j_t, c_t)`, then `(j, a) = (j_t, c_t)`. On the other hand, `alpha_j(J)` is
contained in `nu(j, J u {1..j})`, so this requires `c_t in J u {1..j_t}`.

Choose `j_1 < ... < j_m` and then `c_1, c_2, ...` one at a time, with:
- `c_t > j_t`;
- `c_t` not in `{nu(j_s, c_s) : s < t}`;
- `nu(j_t, c_t)` not in `{c_s : s < t}`, and `nu(j_t, c_t) != c_t`.

Each condition excludes only finitely many values, because `nu` is injective. Then `J = {nu(j_t, c_t)}` is row-free.
(If `nu` is not surjective, any `J` outside its image also works.)

## Step 7. Machine check of the class (calibration)

`experiments/rordam-one-shift-certificates-2026-09-17/porteous_class.py` computes the full class `Delta(E')`, including all
`x_J` terms, in `Z[x]/(x^2)` for `m <= 2`, `r <= 4` and `N <= 4`.

In all 24 cases the class is nonzero iff `(N-1)(r-1) <= m(r+1)`, the dimension of the base. So the primary obstruction is
exactly as strong as the dimension count, with no hidden cancellation. For `N = m+1` it never vanishes. For `m = 1`, `N = 3`
it first vanishes at `r = 4 = 2m+2`, matching Step 5; the grid does not reach `r = 6` for `m = 2`, where the class is
nonzero for all `r <= 4`, as the dimension test predicts.

Calibration at `m = 0` (`p_J = g`, a constant rank-one projection): `nu_1 = 2`. Here `N = 1` is impossible because a rank
of at least 2 is needed. For `N = 2`, the summands `alpha_j(empty) = empty` with `j <= 0` are trivial line bundles, so a
constant section of rank 2 exists. This agrees with `mu(g) <~ Q (+) Q` in Rørdam's Lemma 6.3(i).
