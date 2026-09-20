---
rg: 2
id: lifted-thompson-t-twist-set-is-trivial-or-the-circle-proof
kind: route
title: Tensor, conjugate and diagonalise for the subgroup property; one exact corner kills T's fullness; T MF gives the twist -1 through the rotation centralizer; the dilation takes 2^j-th roots
target: lifted-thompson-t-twist-set-is-trivial-or-the-circle
requires:
  - central-eigencorners-die-over-full-radical-quotients
  - lifted-thompson-t-quotients-are-rotation-centralizers
  - lifted-thompson-t-perfect-centre-cubically-elliptic
  - lifted-thompson-t-mf-radical-dichotomy
  - universal-mf-quotient
---

Throughout, (L1) and (L2) are the lifting facts quoted in
`central-eigencorners-die-over-full-radical-quotients`: unitaries of `Q` lift
to unitaries and projections lift to projections.  The *corner device* is
Steps 1a–1b of `central-eigencorners-die-over-full-radical-quotients-proof`.
If `P != 0` is a projection commuting with `rho(T̄)` and `rho(z) P = mu P`,
then `rho_P(g) = rho(g) P` is a corona representation of `T̄` in the norm
matrix corona `Q_P ≅ PQP`, and `rho_P(z) = mu 1`.  So `mu in Sigma`.

A corona representation `rho` with unitary lifts `U_n(g)` is the same thing
as a sequence of unitary maps `U_n : T̄ -> U(k_n)` with
`||U_n(gh) - U_n(g) U_n(h)|| -> 0` for all `g, h`.  For a unitary `u = [U_n]`
the spectrum is

```text
sp(u) = { mu : liminf_n dist(mu, sp(U_n)) = 0 }.                 (Sp)
```

Here is why.  Since `U_n` is normal, `||(U_n - mu)^(-1)|| = 1/dist(mu, sp U_n)`.
So `u - mu` is invertible in `Q` exactly when these inverses exist and are
bounded for large `n`.  (A bounded coset inverse `[Y_n]` gives
`||(U_n - mu) Y_n - 1|| -> 0`, which forces `dist(mu, sp U_n)` to stay away
from `0`.)

## Item 1: closed subgroups

`1 in Sigma ⊆ S`, via the trivial representation.

- **Products.**  Take `sigma, tau` with `sigma(z) = mu 1` and
  `tau(z) = nu 1`, and unitary lifts `U_n`, `V_n` of sizes `k_n`, `l_n`.  Put
  `W_n(g) = U_n(g) ⊗ V_n(g)` in `M_(k_n l_n)`.  Then
  `||W_n(gh) - W_n(g)W_n(h)|| <= ||U_n(gh) - U_n(g)U_n(h)|| + ||V_n(gh) - V_n(g)V_n(h)||`,
  which tends to `0`, and `||W_n(z) - mu nu|| <= ||U_n(z) - mu|| + ||V_n(z) - nu||`,
  which also tends to `0`.  So `mu nu in Sigma`.

  For `S`, take `mu in sp(rho(z))` and `nu in sp(tau(z))`.  By (Sp) there are
  infinite sets `N_1` and `N_2` of indices along which
  `dist(mu, sp U_n(z)) -> 0` and `dist(nu, sp V_n(z)) -> 0` respectively.
  Restricting a corona representation to an infinite set of coordinates is
  again a corona representation, because the coordinate projection
  `prod_n / (+)_n -> prod_(n in N) / (+)_(n in N)` is a unital
  `*`-homomorphism.  So enumerate `N_1 = {a_1 < a_2 < ...}` and
  `N_2 = {b_1 < b_2 < ...}` and put `W_i = U_(a_i) ⊗ V_(b_i)`.  Since
  `sp(A ⊗ B) = sp(A) sp(B)`, we get
  `dist(mu nu, sp W_i(z)) <= dist(mu, sp U_(a_i)(z)) + dist(nu, sp V_(b_i)(z))`,
  which tends to `0`.  So `mu nu in S`.
- **Inverses.**  Entrywise complex conjugation `X -> X̄` is multiplicative,
  isometric and preserves unitaries.  So `Ū_n` is again asymptotically
  multiplicative, with `Ū_n(z) -> mu̅` (for `Sigma`) and
  `sp(Ū_n(z)) = conj sp(U_n(z))` (for `S`).
- **Closedness.**  Enumerate `T̄ = {g_1, g_2, ...}`.  Let `mu_j -> mu` with
  witnesses `U^(j)_n`.  Choose `n_j` so large that
  `||U^(j)_(n_j)(g_a g_b) - U^(j)_(n_j)(g_a) U^(j)_(n_j)(g_b)|| < 1/j` for all
  `a, b <= j`, and so that also
  - `||U^(j)_(n_j)(z) - mu_j|| < 1/j` in the case of `Sigma`, or
  - `dist(mu_j, sp U^(j)_(n_j)(z)) < 1/j` in the case of `S`, which is
    possible by (Sp).

  The diagonal sequence `(U^(j)_(n_j))_j` is a corona representation, and it
  witnesses `mu`.

## Item 2: scalar dichotomy

**(a) `Sigma != {1}` implies `T` is MF.**  Let `sigma(z) = mu 1` with
`mu != 1`.  Suppose `T` had full radical.  Apply item 1 of
`central-eigencorners-die-over-full-radical-quotients` with `G = T̄`,
`c = z` and `P = 1`.  This is allowed because `T̄` is perfect (item 2 of
`lifted-thompson-t-perfect-centre-cubically-elliptic`), `z` is central and
`T̄/<z> = T` is full.  It gives `sigma(g) = 1` for all `g`, so `mu = 1`, a
contradiction.  So `Rad(T) != T`.  `T` is simple (input (I1) of
`lifted-thompson-t-perfect-centre-cubically-elliptic`) and `Rad(T)` is
normal, so `Rad(T) = 1`.  By `universal-mf-quotient`, `T` is MF.

**(b) `T` MF implies `-1 in Sigma`.**  By
`lifted-thompson-t-quotients-are-rotation-centralizers` there is a
homomorphism `iota_1 : T̄ -> T` with image `C_T(r_1)` and `iota_1(z) = r_1`,
the rotation by `1/2`.  Since `r_1 != 1` and `T` is MF, some corona
representation `pi` of `T` has `pi(r_1) != 1`.  Now `r_1^2 = 1`, so
`pi(r_1)` is a self-adjoint unitary and
`P_- = (1 - pi(r_1))/2` is a nonzero projection.  It commutes with
`pi(C_T(r_1)) = (pi o iota_1)(T̄)` and satisfies `pi(r_1) P_- = -P_-`.
The corner device applied to `rho = pi o iota_1` gives `-1 in Sigma`.

**(c) One twist of order two gives all twists.**  Let `delta(x) = 2x` and
`lambda(g) = delta^(-1) g delta`, that is, `lambda(g)(x) = g(2x)/2`.  It is
an injective endomorphism of `T̄`, with `lambda^j(z) = t_j`, the translation
by `2^(-j)` (see `lifted-thompson-t-quotients-are-rotation-centralizers`).
The element `t_j` is central in the image `lambda^j(T̄)`, and
`t_j^(2^j) = z`.

Let `sigma(z) = -1`.  Put `rho = sigma o lambda^j` and `W = sigma(t_j)`.
Then `W = rho(z)` commutes with `rho(T̄)`, and `W^(2^j) = sigma(z) = -1`.
So `sp(W)` lies in the finite set of `2^j`-th roots of `-1`.  The spectral
projections `E_zeta = chi_{zeta}(W)` lie in `C^*(W) ⊆ rho(T̄)' ∩ Q` and sum
to `1`, so some `E_zeta != 0`.  It satisfies `rho(z) E_zeta = zeta E_zeta`.
The corner device gives `zeta in Sigma` with `zeta^(2^j) = -1`, so
`zeta` has order exactly `2^(j+1)`.

As `j` is arbitrary, `Sigma` is an infinite closed subgroup of `S^1`, so
`Sigma = S^1`.

**Assembly.**
- If `Sigma != {1}`, then (a), (b) and (c) give `Sigma = S^1`.
- If `T` is MF, then (b) and (c) give `Sigma = S^1`.
- `T` is simple and nontrivial, so `Rad(T)` is `1` or `T`.  So "`T` full"
  is the negation of "`T` MF", which by the above is the negation of
  "`Sigma = S^1`", that is, "`Sigma = {1}`".

## Item 3: spectral dichotomy

- **If `T̄` is not MF**, then `Rad(T̄) = T̄` by item 1 of
  `lifted-thompson-t-mf-radical-dichotomy`.  So every corona representation
  is trivial, and `S = {1}`.
- **If `T̄` is MF**, then `z != 1` is moved by some `rho`, and a unitary with
  spectrum `{1}` is `1`, so `S != {1}`.  Suppose `S` were finite.  Then
  `sp(rho(z))` is finite and contains some `mu != 1`, which is isolated.
  Its spectral projection is nonzero and lies in
  `C^*(rho(z)) ⊆ rho(T̄)' ∩ Q`.  The corner device gives `mu in Sigma`, so
  `Sigma = S^1` by item 2.  But `Sigma ⊆ S`, contradicting finiteness.  So
  `S` is an infinite closed subgroup (item 1), and `S = S^1`.
- **Conversely**, `S = S^1` implies `S != {1}`, and hence `T̄` is MF.

∎

## Remarks

- Item 2(c) uses only the dilation.  Taking `2^j`-th roots works for
  every starting twist `mu`, so `mu in Sigma` always gives some square
  root of `mu` in `Sigma`.  That alone does not exclude finite cyclic
  `Sigma` of odd order.  This is why step (b) passes through `-1`.  A general
  `n`-fold version comes from the PL dyadic conjugacy `phi` with
  `phi(x+1) = phi(x) + n`.  For `n = 3`, `phi` has slopes `4` on `[0,1/2]`
  and `2` on `[1/2,1]`, extended periodically.  That version is not needed.
- Nothing here produces an eigencorner out of arc spectrum.  The dichotomy
  converts the flagship's second conjunct into an *existence* statement for
  one scalar-twisted representation
  (`lifted-thompson-t-mf-descends-to-t`); it does not decide it.
