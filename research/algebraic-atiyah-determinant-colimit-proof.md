---
rg: 2
id: algebraic-atiyah-determinant-colimit-proof
kind: route
title: Converge the moments, bound small spectrum through restriction of scalars, and read off the atom
target: algebraic-atiyah-with-determinant-closed-under-colimits
requires: []
---

Notation as in the target.  Group-ring matrices act by right multiplication,
so `r_A r_B = r_(AB)` and `r_A^* = r_(A^*)`.  For a morphism `T` of Hilbert
`N(G)`-modules put

```text
F_T(lambda) = dim_(N(G)) chi_[0,lambda](|T|),        F_T(0) = dim ker T.
```

`F_T(lambda)` is the largest von Neumann dimension of a closed submodule `V`
with `||Tv|| <= lambda ||v||` on `V`: the spectral submodule attains it, and
any such `V` meets the range of `chi_(lambda,infinity)(|T|)` only in `0`, so
projecting `V` onto the complementary range is injective.

**Step 1: subgroups.**  Let `H <= G` and `A in M_(m,n)(Qbar[H])`.  As a left
`H`-space, `l2(G)` is the orthogonal sum of copies of `l2(H)` indexed by the
right cosets `Hg`, and `r_A` acts by the same operator on each copy.  The
vector `delta_e` lies in the copy of the trivial coset, so for every
polynomial `p` the traces of `p(r_A^* r_A)` over `N(G)` and over `N(H)`
agree.  Both spectral measures coincide, and with them the kernel dimensions
and the Fuglede--Kadison determinants.  So `SA`, `Det` and torsion-freeness
pass to subgroups.  (For kernel dimensions this is also the dimension
transfer stated in arXiv:0810.1365, "On the behaviour of the Atiyah
Conjecture under taking subgroups and under taking quotients with finite
kernel".)

**Step 2: a colimit is torsion-free.**  Let `G = colim_i G_i` with every
`G_i` in `A` and structure maps `phi_i: G_i -> G`.  An element of `G_i` is
trivial in `G` exactly when it becomes trivial in some `G_j`, `j >= i`.  If
`g = phi_i(x)` and `g^k = 1`, then the image of `x^k` in some `G_j` is `1`, so
the image of `x` there is `1` by torsion-freeness of `G_j`, and `g = 1`.

**Step 3: `Det` passes to the colimit.**  Lueck, arXiv:2102.04549v2,
Remark 3.11: the determinant conjecture passes to directed colimits, with
structure maps not required to be injective.  The same permanence is used in
`luck-determinant-fixed-tester-proof`.

**Step 4: lift and converge.**  Fix `A in M_(m,n)(Qbar[G])`.  Multiplying by
a positive integer changes no kernel, so assume the coefficients are
algebraic integers, and let `L` be a Galois number field containing them and
their complex conjugates.  Lift the finitely many support elements to some
`G_(i_0)`, and for `j >= i_0` let `A_j in M_(m,n)(O_L[G_j])` be the lifted
matrix.  Let `mu` and `mu_j` be the spectral measures of
`r_(A A^*) = r_A^* r_A` and `r_(A_j A_j^*)` for the unnormalized trace on
`M_m(N(G))`.  All are supported in `[0, kappa_0]`, where `kappa_0` is the
square of the sum of absolute values of all coefficients of `A`, independent
of `j`.  The `k`-th moment of `mu_j` is the identity coefficient of
`trace((A_j A_j^*)^k)`, a finite sum over products of lifted support
elements.  Each such product is `e` in `G` iff it is `e` in `G_j` for all
large `j`, so every moment of `mu_j` is eventually equal to that of `mu`, and
`mu_j -> mu` weakly.  Also `mu({0}) = dim ker r_A` and
`mu_j({0}) = dim ker r_(A_j)`.

**Step 5: uniform control of small spectrum.**  Let `d = [L:Q]`, fix a
`Z`-basis `w_1,...,w_d` of `O_L`, and let `rho: O_L -> M_d(Z)` be the regular
representation.  Applying `rho` entrywise gives integral matrices
`M_j = rho(A_j) in M_(md,nd)(Z[G_j])`.  With the invertible scalar matrix
`P = (sigma_s(w_t))_(s,t)` over the embeddings `sigma_s: L -> C`, one has
`P rho(x) P^(-1) = diag_s sigma_s(x)`, hence

```text
(1 (x) P) r_(M_j) (1 (x) P)^(-1)  =  direct sum over s of r_(sigma_s(A_j)).
```

(i) If `T' = Q_1 T Q_2^(-1)` with bounded invertible module maps, then
`F_T(0) = F_(T')(0)` and `F_T(lambda) <= F_(T')(c lambda)` with
`c = ||Q_1|| ||Q_2^(-1)||`: a submodule `V` witnessing `F_T(lambda)` is sent to
`Q_2 V`, of the same dimension, on which `||T' w|| <= c lambda ||w||`.

(ii) Spectral densities add over orthogonal sums, all terms of
`F(lambda) - F(0)` are nonnegative, and `sigma_s = id` is one summand.

(iii) If an integral matrix `M` with `md` rows has
`det_(N(G_j))(r_M) >= 1` and `||r_M|| <= kappa`, `kappa >= 1`, then for
`0 < lambda < 1`

```text
0 <= log det(r_M) = integral over (0,kappa] of log x dF_M(x)
  <= log(lambda) (F_M(lambda) - F_M(0)) + md log(kappa),
```

so `F_M(lambda) - F_M(0) <= md log(kappa) / |log lambda|`.

Take `kappa` to be the sum of absolute values of the integer coefficients of
`rho(A)`, and `c` from `P`.  `Det(G_j)` applies to `M_j`, and (i)--(iii) give,
for every `j` and every `lambda` with `c lambda < 1`,

```text
mu_j((0, lambda^2]) = F_(A_j)(lambda) - F_(A_j)(0) <= md log(kappa) / |log(c lambda)|.
```

**Step 6: the atom.**  Weak convergence gives `mu({0}) >= limsup_j mu_j({0})`
for the closed set `{0}`, and for the open set `(-1, lambda^2)`

```text
mu({0}) <= mu((-1, lambda^2)) <= liminf_j mu_j((-1, lambda^2))
        <= liminf_j mu_j({0}) + md log(kappa) / |log(c lambda)|.
```

Letting `lambda -> 0` gives `mu({0}) = lim_j mu_j({0})`.  Each `mu_j({0})` is
an integer by `SA(G_j)`, so `dim ker r_A` is an integer.  Thus `SA(G)`, and
with Steps 2 and 3, `G` lies in `A`.  QED
