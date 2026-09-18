---
rg: 2
id: toms-wide-sibling-cubes-fill-proof
kind: route
title: Replace the band space by an open set of Hermitian matrices, filter it by the number of non-negative eigenvalues, compute each layer by Alexander duality, then run obstruction theory on the cube
target: toms-wide-sibling-cubes-fill-without-common-drop
requires: []
---

Notation is from the target. `H` is the real vector space of Hermitian `n x n` matrices,
of dimension `n^2`, with eigenvalues `lambda_1 >= ... >= lambda_n`. Put `lambda_(n+1) = -infinity`.

**Step 1 (an open model).** Let `Y_N = { A in H : lambda_(g+1)(A) > 0 > lambda_(g+N+1)(A) }`.
This is open in `H`. Define two maps.
- `phi : X_(g,N) -> Y_N` by `phi(Q) = Q - epsilon(Q)`, with `epsilon(Q) = lambda_(g+1)(Q)/2`.
- `psi : Y_N -> X_(g,N)` by `psi(A) = A_+`, the positive part. The rank of `A_+` is the
  number of positive eigenvalues, which lies in `[g+1, g+N]`.

Both maps are continuous. The composite `psi phi (Q) = (Q - epsilon)_+` is joined to `Q` by
`(Q - s epsilon)_+`, `s in [0,1]`. Its rank lies between `g + 1` (since `lambda_(g+1) = 2 epsilon > s epsilon`)
and `rank Q`. The composite `phi psi (A)` is joined to `A` by `(1-t) A + t (A_+ - epsilon(A_+))`.
This path is a monotone function of `A`, so it keeps the order of the eigenvalues. It keeps
`lambda_(g+1) >= lambda_(g+1)(A)/2 > 0`, and it sends every eigenvalue `<= 0` to a negative
number when `t > 0`. So `X_(g,N) ≃ Y_N`.

**Step 2 (the filtration).** `Y_1 ⊂ Y_2 ⊂ ... ⊂ Y_(n-g) = O = { lambda_(g+1) > 0 }`. Each `Y_r`
is open in `H`. `O` is star-shaped about the identity, since
`lambda_(g+1)((1-t) A + t) = (1-t) lambda_(g+1)(A) + t`. So `O` is contractible. The layer

```text
Z_r = Y_r \ Y_(r-1) = { lambda_(g+1) > 0,  lambda_(g+r) >= 0 > lambda_(g+r+1) }
```

is closed in `Y_r`.

**Step 3 (each layer by duality).** Put `M = g + r`. On `Z_r` the eigenvalue gap at `0` makes
the non-negative spectral subspace `V` (of dimension `M`) continuous. So `Z_r` is a fibre
bundle over the Grassmannian `Gr_M(C^n)`, of real dimension `2M(n-M)`, with fibre
`F = F_+ x F_-`.
- `F_-` is the negative definite cone on `V^perp`. It is homeomorphic to `R^((n-M)^2)`.
- `F_+` is the set of positive semidefinite `B` on `V` with `rank B >= g + 1`. Write `B = t x`
  with `t = tr B > 0` and `x` in the density matrices `Delta` of `V`. This gives
  `F_+ ≅ (0, infinity) x (Delta \ A)`, where `A ⊂ ∂Delta` is the compact set of density matrices
  of rank at most `g`.

`Delta` is a compact convex body of dimension `M^2 - 1`. `A` is compact semialgebraic, of
dimension `a = 2g(M-g) + g^2 - 1` (the rank-`g` stratum; `a = -1`, `A` empty, when `g = 0`).
Compact supports give

```text
H_c^i(F_+) = H_c^(i-1)(Delta \ A) = H^(i-1)(Delta, A) = H~^(i-2)(A)   (Cech),
```

which is `0` for `i >= a + 3`. So `H_c^q(F) = 0` for `q >= (n-M)^2 + a + 3`. The Leray
spectral sequence with compact supports over the compact, simply connected base then gives
`H_c^i(Z_r) = 0` for `i >= 2M(n-M) + (n-M)^2 + a + 3`.

`Y_r` is an oriented `n^2`-manifold, and `Z_r` is closed in it with complement `Y_(r-1)`.
Alexander–Lefschetz duality gives `H_k(Y_r, Y_(r-1); Z) ≅ H_c^(n^2-k)(Z_r; Z)`, with Cech
cohomology with compact supports of the closed set `Z_r`. Now

```text
n^2 - 2M(n-M) - (n-M)^2 = M^2,       M^2 - a - 3 = (M - g)^2 - 2 = r^2 - 2.
```

So `H_k(Y_r, Y_(r-1)) = 0` for `k <= r^2 - 2`. In the top degree `k = r^2 - 1` the group is
`H^top(Gr) ⊗ H_c^top(F) = Z`. Here `H_c^top(F_+) = H^a(A) = Z`, because the rank-`g` stratum
of `A` is an open, dense, connected, orientable `a`-manifold (a ball bundle over
`Gr_g(C^M)`), and the lower strata have codimension `2r + 1 >= 3`.

**Step 4 (homology of `Y_N`).** The triples `(O, Y_(r), Y_(r-1))` for `r >= N + 1` and Step 3
give `H_k(O, Y_N) = 0` for `k <= (N+1)^2 - 2`. Since `O` is contractible,
`H~_i(Y_N) ≅ H_(i+1)(O, Y_N)`, which vanishes for `i <= (N+1)^2 - 3 = D`. One degree up,
`H_(D+2)(O, Y_(N+1)) = H_(D+3)(O, Y_(N+1)) = 0`, since `D + 3 <= (N+2)^2 - 2`. So
`H_(D+1)(Y_N) ≅ H_(D+2)(Y_(N+1), Y_N) = Z`. If `n <= g + N`, then `Y_N = O` is contractible,
and nothing is to be shown.

**Step 5 (simple connectivity).** The cover `U_k = { lambda_(g+k) > lambda_(g+k+1) }` of
`X_(g,N)` has all intersections `U_T` non-empty and homotopy equivalent to partial flag
manifolds. These are connected and simply connected. By van Kampen for open covers with
path-connected intersections, `pi_1(X) = 1`. With Step 4 and Hurewicz, `X` is `D`-connected
and `pi_(D+1)(X) = Z`. This proves Theorem A's first two statements.

*Rational dual.* `H^(D+1)(X; Q) = Q`. The class `Omega` of
`toms-sibling-cube-swap-drops-add-to-depth-n` with exponents `(1, 2, ..., N)` lies in this
degree, since `N - 1 + 2 sum k = N^2 + 2N - 1 = D + 1`. It is non-zero, because
`e^* Omega != 0` when every `j_nu = N`. So `Omega` spans `H^(D+1)(X; Q)`.

*Check.* `band_e2.py` computes the `E_2` page of the cover. Over `Z` it agrees with Steps
4 and 5 for `N = 1, 2, 3` and all tested `g`. For `N = 4` with stable `g` it agrees over `F_p`
for seven primes, including `1000000007`.

**Step 6 (Theorem B).** Triangulate `K = S x Y` with `L = ∂S x Y` as a subcomplex. A map
`L -> X` extends over `K` once the obstruction groups `H^k(K, L; pi_(k-1)(X))` vanish for all
`k <= dim K = d`. By Step 5, `pi_(k-1)(X) = 0` for `k - 1 <= D`, so every group vanishes when
`d <= D + 1`. The extension lands in `X_(g,N)(n)` for the `n` of `e` (Theorem A holds for
every `n >= g + 1`). It is a positive element of `M_n(C(S x Y))` that equals `e` on
`∂S x Y` and has rank in `[g+1, g+N]`.

**Step 7 (Theorem C).** Let `d = D + 2`. `X` is `D`-connected and simple, with
`pi_(D+1)(X) = Z`. Let `iota in H^(D+1)(X; Z) = Z` be the fundamental class. The first
obstruction to extending `e` is `delta(e^* iota) in H^(D+2)(K, L; Z)`, and there are no
further obstructions, since `K` has no cells of dimension above `D + 2`. By the exact
sequence of `(K, L)`, `delta(e^* iota) = 0` iff `e^* iota` is restricted from
`H^(D+1)(K) = H^(D+1)(Y)`. That is, iff its component in `H^(N-1)(S^(N-1)) ⊗ H^(D+2-N)(Y)`
vanishes. These groups are torsion-free, so this can be tested rationally, where
`iota = lambda Omega` with `lambda != 0` (Step 5). The class `Omega` lies in filtration
`N - 1`, so `e^* Omega` has only this component, and the cube theorem computes it:

```text
e^* Omega = ± prod_k (alpha^k - beta^k) · det[u_nu^k]_(k, nu = 1..N).
```

The alternant has degree `2 sum k = N(N+1) = 2 sum j_nu`, the top degree of `Y`. Its
monomials `prod_nu u_nu^(pi(nu))` are distinct, so no two cancel. In top degree such a
monomial is non-zero exactly when `pi(nu) = j_nu` for every `nu`. So the alternant is
non-zero exactly when `{j_nu} = {1, ..., N}` as multisets.

**Step 8 (corollaries).** For equal `j`: `d = N + 2Nj <= D + 1 = N^2 + 2N - 1` iff
`2Nj <= N^2 + N - 1`, iff `N >= 2j`. At `N = 2j - 1` we have `d = D + 2`, and
`(j, ..., j) = (1, ..., N)` only when `N = j = 1`. The forced range `N <= j` is the cube
theorem. The Hall condition of the cube theorem gives `sum j_nu >= N(N+1)/2`, so it never
meets the range of Step 6.

For `alpha = -beta` the factor `alpha^2 - beta^2` is `0`, so `e^* iota = 0` at `d = D + 2` once
`N >= 2`. At Toms's bottom level `j_n = 2 d_n^2`, so `N >= 4 d_n^2 - 1` bottom siblings
fill. Square.
