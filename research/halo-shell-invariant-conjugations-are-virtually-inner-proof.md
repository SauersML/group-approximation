---
rg: 2
id: halo-shell-invariant-conjugations-are-virtually-inner-proof
kind: route
title: Replace the site permutation by a finitary one that agrees on a finite support, and take its order as the power
target: halo-shell-invariant-conjugations-are-virtually-inner
requires: []
artifacts:
  - research/artifacts/linton-halo-contraction-obstruction-2026-09-16.md
---

Full proofs are in Sections 2--3 of the artifact.  Convention:
`c_g(x) = g x g^-1`.  Transport everything to `L(X)` through `theta`.

**(1)**

- *Finite support.*  `L(X)` is the directed union of the pieces `L(Y)`, `Y`
  finite, by monotonicity and generation by finite pieces.  So there is one
  finite `Y` with `H <= L(Y)`.
- *Agreement on a piece.*  If bijections `sigma, tau` of `X` agree on `Y`, then
  `sigma o iota_Y = tau o iota_Y`.  By functoriality `L(sigma)` and `L(tau)`
  agree on `L(Y)`.
- *Finitary replacement.*  Write `e = rho f` with `rho` in `R` and `f` in `F0`.
  Put `Y' = Y cup pi(f)(Y)`.  Extend `pi(f)|_Y` to a permutation of `Y'` by
  mapping `Y' \ Y` bijectively onto `Y' \ pi(f)(Y)`, and extend by the identity
  outside `Y'`.  The result `sigma` has finite support, so finite order `N`, and
  agrees with `pi(f)` on `Y`.
- *Compare conjugations.*  In `P = L(X) semidirect Sym(X)` put
  `eps = (r, sigma)` with `r = theta^-1(rho)`.  On `L(X)`,
  `c_eps = c_r o L(sigma)`, while `c_e` transports to `c_r o L(pi(f))`.  These
  agree on `L(Y)`, hence on `H`, and `c_e` maps `H` into `H`.  By induction,
  `c_e^k|_H = c_eps^k|_H` for all `k >= 0`.
- *The power.*  `eps^N = (r L(sigma)(r) ... L(sigma^(N-1))(r), 1) = (r_sigma, 1)`.
  So `c_e^N|_H = c_(r_sigma)|_H`, and `rho' = theta(r_sigma)` works.

**(2)**  `N_R(H) = N_E(H) cap R` and `C_E(H)` are normal in `N_E(H)`.  For
`e` in `N_E(H)`, take `N` and `rho'` from (1).  Then `rho' H rho'^-1 = H`, so
`rho'` lies in `N_R(H)`, and `rho'^-1 e^N` centralizes `H`.

**(3)**  Suppose `H != 1` and `rho H rho^-1 < H` is strict.  Put
`psi = c_rho|_H`, injective and not onto.

- *No power of `rho` lies in `H`.*  We have `rho^j H rho^-j < H` for
  `j >= 1`.  If `rho^j` lay in `H`, conjugation by it would preserve `H`.  The
  case `j <= -1` follows by inversion.
- *`D = <H, rho>` is the ascending HNN extension*
  `M = <H, t | t h t^-1 = psi(h)>`.  The map `t -> rho` is onto `D`.  Every
  element of `M` has the form `t^-m h t^k` with `m, k >= 0`, using
  `t h = psi(h) t` and `h t^-1 = t^-1 psi(h)`.  If `rho^-m h rho^k = 1` then
  `h = rho^(m-k)`, so `m = k` and `h = 1`.
- *Homology.*  `D` is finitely generated in `R`, so free of rank `d >= 1`.
  Put `r = rank(H)`.  `H_2(H;Q) = 0`, so the rational Mayer--Vietoris sequence
  of the HNN extension gives
  `0 -> H_2(M) -> H_1(H) --(psi_* - 1)--> H_1(H) -> H_1(M) -> Q --0--> Q`.
  Since `M = D` is free, `H_2(M;Q) = 0`, so `psi_* - 1` has rank `r` and
  `dim H_1(M;Q) = 1`.  So `d = 1`, and `D` is abelian.  Hence
  `rho H rho^-1 = H`, a contradiction.

**(4)**  With `N, rho'` from (1),
`rho' H rho'^-1 = e^N H e^-N <= e H e^-1 <= H`.  By (3) the outer terms are
equal, so `e H e^-1 = H`.
