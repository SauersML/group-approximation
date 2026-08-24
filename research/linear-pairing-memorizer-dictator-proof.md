---
rg: 2
id: linear-pairing-memorizer-dictator-proof
kind: route
title: Average the r-fold pair products over the complement of the base pair
target: linear-pairing-memorizer-restricts-to-a-dictator
requires: []
---

Direct verification of `(M1)`--`(M4)`.

Fix `b != 0`.  The `b`-pairs `{u, u+b}` partition `Omega`, so `|P_b| = N/2`,
and `C_b = {0,b}` is the pair containing `0`.  For
`A subset P_b \ {C_b}` with `|A| = r`, write
`prod_A(X) = prod_{{u,u+b} in A} X_u X_{u+b}` and let `supp(A)` be the union
of the pairs in `A`, a `2r`-element set disjoint from `{0, b}`.  There are
`M = binom(N/2 - 1, r)` such `A`.

**(M1) Boundedness.**  Each `prod_A(X) in {-1,1}`, so the average over the
`M` sets lies in `[-1,1]`, and multiplying by `X_0 in {-1,1}` preserves
that.

**(M2) Homogeneity of degree 2r+1.**  As a multilinear polynomial,
`X_0 * prod_A(X)` is the character of the set `{0} union supp(A)`, of size
`1 + 2r` since `0 notin supp(A)`.  Distinct `A` give distinct `supp(A)`,
hence distinct characters, so

```text
B_{b,r} = (1/M) * sum_A chi_{{0} union supp(A)}
```

is a sum of `M` distinct characters, each of the same size `2r+1`, each
with coefficient `1/M`.  In particular no cancellation and no collision
occurs, which is what makes the remaining computations exact.

**(M3) Restriction.**  On `D_b` we have `X_u = X_{u+b}` for every `u`, so
`X_u X_{u+b} = 1` and `prod_A(X) = 1` for every `A`.  The average is `1`
and `B_{b,r}|_{D_b} = X_0`, the quotient coordinate indexed by `C_b`.

**(M4) L^2 norm.**  By Parseval over the `M` distinct characters,
`||B_{b,r}||_2^2 = M * (1/M)^2 = 1/M`.  For fixed `r`,
`M = binom(N/2 - 1, r) = Theta_r(N^r)`, so `||B_{b,r}||_2^2 = Theta_r(N^{-r})`.

**The three consequences.**

*Influence.*  `Inf(B_{b,r}) = sum_S |hat B(S)|^2 |S| = M * (1/M^2) * (2r+1)
= (2r+1)/M`, while the restriction is a dictator of total influence 1.  So
no bound `Inf(f|_{D_b}) <= C * Inf(f)` with `C` independent of `k` is
possible, at fixed degree and with `f` bounded.

*Noise.*  By `(M2)` every character in the expansion has size `2r+1`, hence
`T_rho B_{b,r} = rho^(2r+1) B_{b,r}` exactly.  With `f = B_{b,r}` and
`g = T_rho f` we get `g|_{D_b} = rho^(2r+1) X_0`, so
`Inf^{<=d}_{C_b}(g|_{D_b}) = rho^(2(2r+1))` for every `d >= 1`, a constant
independent of `k`.

*No ambient influential coordinate.*  Every character in the expansion has
coefficient `1/M`, and each coordinate `x` lies in
`binom(N/2 - 2, r-1)` of them if `x notin {0,b}`, and in all `M` of them if
`x = 0`.  Either way `Inf_x(B_{b,r}) <= 1/M -> 0` after multiplying count by
`(1/M)^2`; concretely `Inf_0 = M * (1/M)^2 = 1/M`.  So at any fixed
threshold the set of ambient low-degree influential coordinates is empty.
