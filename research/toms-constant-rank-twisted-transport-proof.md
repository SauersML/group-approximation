---
rg: 2
id: toms-constant-rank-twisted-transport-proof
kind: route
title: Constant rank makes the support bundle continuous and constant over the family, and root multiplicities of its total Chern class bound the swapped halves
target: toms-constant-rank-twisted-transport-costs-double-rank
requires: []
---

Notation is from the target. `V(C)` denotes Murray–von Neumann classes of projections.

**Step 1 (continuous support).** Put `K = Z x CP^j`. `Q|K` is positive in
`M_k(C(K))` with constant rank `m`. Its ordered eigenvalues are continuous, and
`lambda_m > 0` on `K`, so `lambda_m >= delta > 0` on the compact `K`, while
`lambda_(m+1) ≡ 0`. With `f` continuous, `f = 0` on `[0, delta/3]` and `f = 1` on
`[2 delta/3, ∞)`, the element `p = f(Q|K)` is a projection of rank `m`, and
`Q|K ~ p` in the Cuntz sense. Write `p_z = p|({z} x CP^j) in M_k(C(CP^j))`.

**Step 2 (constant class).** `z -> p_z` is norm-continuous on `Z`, by uniform
continuity of `p` on the compact `K`. Projections at distance `< 1` are unitarily
equivalent, so `z -> [p_z] in V(C(CP^j))` is locally constant and hence constant on
the connected `Z`. So `E_0 := range p_(z_0) ≅ E_1 := range p_(z_1)`.

**Step 3 (sub-bundles).** Restriction to a slice is a `*`-homomorphism, so
`e_i <~ P|slice_i <~ Q|slice_i ~ p_(z_i)`. For projections, Cuntz subequivalence
is Murray–von Neumann subequivalence. So `range(e_i) = L_1^(p_i) ⊕ L_2^(q_i)` is
isomorphic to a sub-bundle of `E_i`, with complement `S_i` of rank
`s_i = m - p_i - q_i >= 0`.

**Step 4 (roots).** In `H^*(CP^j; Z) = Z[u]/(u^(j+1))`,

```text
(1 + alpha u)^(p_0) (1 + beta u)^(q_0) c(S_0)  =  (1 + alpha u)^(p_1) (1 + beta u)^(q_1) c(S_1).
```

`c(S_i)` has constant term `1` and degree at most `rank S_i = s_i`. Both sides are
polynomials of degree at most `m <= j`, so the equality holds in `Z[u]`. Let
`nu_i` be the multiplicity of the root `-1/beta` in `c(S_i)`, so `0 <= nu_i <= s_i`.
Since `alpha != beta`, `1 + alpha u` does not vanish at `-1/beta`. Comparing
multiplicities gives `q_0 + nu_0 = q_1 + nu_1`, so `q_0 - q_1 = nu_1 - nu_0 in [-s_0, s_1]`.
If `alpha != 0`, the root `-1/alpha` gives the same for `p`. This proves the theorem.

**Step 5 (swap corollary).** At `z_0 = (x, y)`,
`phi_(M-1)(a')|slice = a'(x) tensor gamma_1 + a'(y) tensor gamma_2`, a sum of
orthogonal elements with constant matrix coefficients. Let `R_x = rank a'(x)`,
`R_y = rank a'(y)`, and let `delta` be below every positive eigenvalue of
`a'(x)` and `a'(y)`. Then

```text
e_0 = supp a'(x) tensor gamma_1 + supp a'(y) tensor gamma_2  <=  delta^(-1) phi_(M-1)(a')|slice,
```

so `e_0 <~ P|slice_0`, with `(p_0, q_0) = (R_x, R_y)`. At `z_1 = (y, x)` the same
construction gives `(p_1, q_1) = (R_y, R_x)`. Step 4 gives
`R_y - R_x <= s_1 = m - R_x - R_y`, so `m >= 2 R_y`, and
`R_y - R_x >= -s_0 = -(m - R_x - R_y)`, so `m >= 2 R_x`.

**Step 6 (point traces).** For `w in X_M`, extend `w` beyond stage `M` by diagonal
points with the projective coordinates fixed. These points are compatible with the
coordinate projections, and `phi` at a diagonal point is `b(w) tensor (gamma_1 + gamma_2)`.
So `tau_w(b) = tr b(w) / r_M` defines a trace on `A`, with
`d_(tau_w)(b) = rank b(w) / r_M` and `tau_w(h) = F_M(w)`, the leaf average. At
`w = (x(s), x(1 - s), y)` every leaf of the first copy is `c(s)` and every leaf of
the second is `c(1 - s)`, so `F_M(w) = (s + (1 - s))/2 = 1/2`.

**Step 7 (consequence).** Let `a_n in M_k(A_(N_n))_+` with `[a_n]` increasing and
`d_tau(a_n) -> tau(h)`, and `[a_n] <= [a]`.
- *Upper band.* `d_(tau_w)(a_(n+1)) <= tau_w(h)`, so on `Z x CP^j` the rank of
  `a_(n+1)` at stage `M` is at most `r_M / 2 = r_(M-1) <= 2 r_(M-1)^2 = j`.
- *Lower band.* `d_tau` preserves suprema, so `rank a_n(x(1)^(N_n)) / r_(N_n) -> h(c(1)) = 1`.
  Fix `n` with this ratio `> 1/2`, and `eps` below the positive spectrum of
  `a_n(x(1)^(N_n))`.
- *Stage.* `a_n <~ a_(n+1)` in `A tensor K` gives `v` with `||a_n - v a_(n+1) v*|| < eps`.
  Approximating `v` at a finite stage and using that limit norms are limits of stage
  norms, there are arbitrarily large `M` with
  `(phi_(N_n,M)(a_n) - eps)_+ <~ phi_(N_(n+1),M)(a_(n+1))` in `M_k(A_M)`.
- *Contradiction.* Put `a' = phi_(N_n,M-1)((a_n - eps)_+)`. Diagonal pushforward
  doubles rank at each stage, so
  `rank a'(x(1)) = 2^(M-1-N_n) rank a_n(x(1)^(N_n)) > r_(M-1)/2`. `Z` is an arc
  from `(x(0), x(1))` to `(x(1), x(0))`. If `rank a_(n+1)` were a constant `m` on
  `Z x CP^j`, Step 5 would give `m > r_(M-1)`, contradicting the upper band. Square.
