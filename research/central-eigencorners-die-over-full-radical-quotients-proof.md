---
rg: 2
id: central-eigencorners-die-over-full-radical-quotients-proof
kind: route
title: Cut the representation down to the eigencorner, tensor it with its conjugate to kill the central phase, and let full radical of the quotient flatten the corner to scalars
target: central-eigencorners-die-over-full-radical-quotients
requires:
  - lifted-thompson-t-quotients-are-rotation-centralizers
  - lifted-thompson-t-perfect-centre-cubically-elliptic
---

Notation as in the target: `G` countable and perfect, `c in Z(G)`, and
`G/<c>` with full radical.  `Q = prod_n M_(k_n) / (+)_n M_(k_n)` with quotient
map `x = (x_n) -> [x]`.  Two standard facts about `Q` are used.
- (L1) Every unitary of `Q` lifts to a sequence of unitaries.  Take any lift
  `(x_n)`.  Then `||x_n^* x_n - 1|| -> 0`, so `x_n` is eventually invertible
  and its polar part `x_n |x_n|^(-1)` is a unitary lift.
- (L2) Every projection of `Q` lifts to a sequence of projections.  Take a
  self-adjoint lift `(a_n)`.  Then `||a_n^2 - a_n|| -> 0`, so eventually
  `sp(a_n)` avoids `1/2`, and the spectral projection `chi_(>1/2)(a_n)` is
  within `o(1)` of `a_n`.

## Item 1

Let `rho`, `P`, `lambda` be as in item 1, and assume `P != 0`.  Otherwise
there is nothing to prove.

**Step 1a (the corner is a corona).**  By (L2) lift `P` to projections `P_n`
of rank `r_n`.  Let `J = {n : r_n >= 1}`.  It is infinite, since `P != 0`.
Put `Q_P = prod_(n in J) M_(r_n) / (+)_(n in J) M_(r_n)`.  Identify
`P_n M_(k_n) P_n` with `M_(r_n)`.  Then the map `[x] -> [(P_n x_n P_n)_(n in J)]`
is a unital `*`-isomorphism `PQP -> Q_P`.
- It is well defined and a `*`-homomorphism, because `x -> P x P` is
  multiplicative on `P Q P`.
- It is onto.
- Its kernel consists of the `P x P` with `||P_n x_n P_n|| -> 0` along `J`.
  Off `J` those coordinates are `0`, so `P x P = 0` in `Q`.

So `Q_P` is again a norm matrix corona.

**Step 1b (the corner representation).**  `P` commutes with `rho(G)`, so
`rho_P(g) = rho(g) P` is a unitary of `PQP` and
`rho_P(g) rho_P(h) = rho(g) rho(h) P = rho_P(gh)`.  Hence `rho_P` is a
corona representation of `G` in `Q_P`, and `rho_P(c) = lambda P`.  Since
`rho_P(c)` is unitary and `P != 0`, we get `|lambda| = 1`.

**Step 1c (conjugate tensor).**  By (L1) choose unitary lifts
`u_n(g) in U(r_n)`, `n in J`, of `rho_P(g)`.  Two estimates are used.
- For unitaries `U, V`,
  `||U (x) conj(U) - V (x) conj(V)|| <= 2 ||U - V||`.  Insert `V (x) conj(U)`.
- `(U (x) conj U)(V (x) conj V) = UV (x) conj(UV)`.

Put `sigma(g) = [(u_n(g) (x) conj(u_n(g)))_(n in J)]` in the corona
`prod_J M_(r_n^2) / (+)_J M_(r_n^2)`.  The first estimate makes `sigma(g)`
independent of the lift.  The two together give
`||sigma_n(g) sigma_n(h) - sigma_n(gh)|| <= 2 ||u_n(g) u_n(h) - u_n(gh)|| -> 0`.
So `sigma` is a corona representation of `G`.

Now `||u_n(c) - lambda 1|| -> 0`.  So
`||sigma_n(c) - lambda conj(lambda) 1|| <= 2 ||u_n(c) - lambda 1|| -> 0`,
and since `|lambda| = 1` this says `sigma(c) = 1`.  Therefore `sigma` kills
the normal subgroup `<c>` (central, hence normal) and factors through
`G/<c>`.  By hypothesis `G/<c>` has full radical, so `sigma` is trivial:

```text
||u_n(g) (x) conj(u_n(g)) - 1|| -> 0          for every g in G.       (T1)
```

**Step 1d (flattening).**  Let `U` be a unitary of `M_r` with eigenvalues
`mu_1, ..., mu_r`.  Then `U (x) conj U` is unitary with eigenvalues
`mu_i conj(mu_j)`, so

```text
||U (x) conj U - 1|| = max_(i,j) |mu_i - mu_j|   and   ||U - mu_1 1|| = max_i |mu_i - mu_1|.
```

So by (T1) there are scalars `a_n(g)`, with `|a_n(g)| = 1`, satisfying
`||u_n(g) - a_n(g) 1|| -> 0`.  Scalars commute, so for `g, h in G`,

```text
||u_n(g) u_n(h) - u_n(h) u_n(g)|| <= 2 ||u_n(g) - a_n(g)|| + 2 ||u_n(h) - a_n(h)|| -> 0.
```

Hence `rho_P(g)` and `rho_P(h)` commute in `PQP`.  So `rho_P([g,h]) = P`
for all `g, h`, and `rho_P` is trivial on `[G, G] = G` because `G` is perfect.
That is, `rho(g) P = P` for every `g`.  With `g = c` this gives
`lambda P = P`, so `lambda = 1`. ∎

## Item 2

Let `c` have order `m < infinity` and let `rho` be a corona representation of
`G`.  Then `rho(c)^m = 1`, so `sp(rho(c))` lies in the finite set of `m`-th
roots of unity.  For each `lambda` in the spectrum, the spectral projection
`P_lambda = chi_({lambda})(rho(c))` lies in `C^*(rho(c), 1)`, because
`lambda` is isolated.  Since `c` is central, `rho(c)` commutes with `rho(G)`,
so `P_lambda in rho(G)' ∩ Q`.  Moreover `rho(c) P_lambda = lambda P_lambda`
and `sum_lambda P_lambda = 1`.  By item 1, `rho(g) P_lambda = P_lambda` for
every `lambda`, and summing gives `rho(g) = 1`.  So every corona
representation of `G` is trivial. ∎

## Item 3

Suppose `lambda != 1` is an isolated point of `sp(rho(c))`.  Then
`P = chi_({lambda})(rho(c))` is a nonzero projection in
`C^*(rho(c), 1) <= rho(G)' ∩ Q`.  The element `rho(c) P` is normal in
`PQP` with spectrum `{lambda}`, so `rho(c) P = lambda P`.  Item 1 gives
`lambda = 1`, a contradiction.

If `rho(c) = lambda 1` is a scalar, apply item 1 with `P = 1`.  This gives
`rho(g) = 1` for all `g`. ∎

## Item 4

Fix `k >= 0` and put `G = C_T(r_k)`.
- By `lifted-thompson-t-quotients-are-rotation-centralizers`, the map
  `iota_k` induces `T̄/<z^(2^k)> ≅ C_T(r_k)`, with `z -> r_k`.
- Since `z` has infinite order (`z^j(0) = j`), `r_k` has order exactly
  `2^k` in `G`, and `r_k` is central in `G`.
- `G` is perfect, being a quotient of `T̄`, which is perfect by item 2 of
  `lifted-thompson-t-perfect-centre-cubically-elliptic`.
- `G/<r_k> ≅ T̄/<z> = T`.

So if `T` has full radical, item 2 applies with `c = r_k` and gives full
radical for `C_T(r_k)`.

Conversely, `C_T(r_k) -> C_T(r_k)/<r_k> ≅ T` is onto.  For every corona
representation `pi` of `T`, the composite `pi o q` is a corona
representation of `C_T(r_k)`.  If `C_T(r_k)` has full radical this composite
is trivial, and since `q` is onto, `pi` is trivial.  So `T` has full
radical. ∎

## Kazhdan hygiene

The proof uses (L1), (L2), finite-dimensional spectral theory, perfectness
of `T̄`, and the rotation-centralizer isomorphism.  It uses no Property
`(T)`, no trace and no spectral gap.
