---
rg: 2
id: lift-yes-set-load-rigidity-proof
kind: route
title: Bound a_uv by l_u times the indicator that the other fibre is non-empty, use E l = 1 to make the support nearly closed and the loads constant along all but a 2 eta fraction of edges, and read the canonical labeling off the load-one part
target: lift-yes-sets-are-labelings-unless-the-base-loses-a-cut
requires: []
artifacts:
  - experiments/sse-lift-base-gate-2026-09-18/check_load_rigidity.py
---

Notation is that of the target claim. Only three facts about `H` are used: the
directed-edge law is symmetric, its marginal is `mu`, and `E_mu l = 1` because
`|S| = |V|`. So everything below holds verbatim for reversible weighted chains
at exact volume.

## (0) The two elementary bounds

`L` has stationary measure `mu(u)/q` and edge law `(u,i) -> (v, pi_uv(i))` with
`(u,v)` a random edge and `i` uniform on `[q]`. For `S` of measure `1/q`,
`1 - Phi_L(S) = E_(u,v)[a_uv]` (item (0) of
`lifts-over-multiscale-expanders-proof`). Write `M = min(l_u, l_v)` and
`X = max(l_u, l_v)` on a random edge.

- Because `pi_uv` is injective, `a_uv <= M`.
- Because `S_v` is empty off `P`, `a_uv = 0` whenever `v not in P`. Combining,
  `a_uv <= l_u 1(v in P)`.
- Because the edge law is symmetric with marginal `mu`,
  `E[l_u] = E[l_v] = E_mu l = 1`, so `E[M] + E[X] = 2`.

## (1) Load-weighted escape

```text
1 - eta = E[a] <= E[l_u 1(v in P)] = E[l_u] - E[l_u 1(v not in P)]
        = 1 - E[l_u 1(v not in P)],
```

so `E[l_u 1(v not in P)] <= eta`. That is item (1).

## (2) The support is nearly closed

`l_u >= 1` for `u in P`, so

```text
Pr[u in P, v not in P] = E[1(u in P) 1(v not in P)]
                      <= E[l_u 1(u in P) 1(v not in P)]
                       = E[l_u 1(v not in P)] <= eta,
```

using `l_u 1(u in P) = l_u`. The edge law is symmetric, so
`Pr[u in P, v not in P] = Pr[u not in P, v in P] = Pr[u in A_0, v not in A_0]`,
and by definition `Pr[u in A, v not in A] = mu(A) Phi_H(A)`. Applying it to
`A = P` and to `A = A_0` gives item (2).

## (3) Load integrality and mass balance

`E[M] >= E[a] = 1 - eta`, hence `E[X - M] = 2 - 2 E[M] <= 2 eta`. The loads are
integers, so `X - M >= 1` whenever `l_u != l_v`, and Markov gives
`Pr[l_u != l_v] <= E[X - M] <= 2 eta`.

Let `A_j = {v : l_v = j}`. From `E l = 1`,

```text
sum_(j >= 2) j mu(A_j) = E[l] - mu(A_1) = 1 - mu(A_1) = zeta,
mu(A_0) + mu(A_1) + mu({l >= 2}) = 1  ==>  mu(A_0) + mu({l >= 2}) = zeta.
```

Since `mu({l >= 2}) = sum_(j >= 2) mu(A_j) <= (1/2) sum_(j >= 2) j mu(A_j)
= zeta/2`, we get `mu(A_0) >= zeta/2`, i.e. `zeta <= 2 beta`. This is item (3).

## (4) Rounding by the canonical labeling

Let `x(v)` be the unique element of `S_v` for `v in A_1`, and `0` otherwise.
On an edge with `u, v in A_1` we have `M = 1`, so `a_uv in {0,1}` and
`a_uv = 1` exactly when `pi_uv(x(u)) = x(v)`. Therefore

```text
val(x) = Pr[pi_uv(x(u)) = x(v)] >= E[a_uv 1(u in A_1, v in A_1)].
```

Bound the missing part by `a_uv <= M <= l_u` and `a_uv <= M <= l_v`:

```text
E[a 1(u not in A_1)] <= E[l_u 1(l_u != 1)] = E[l 1(l != 1)] = 1 - mu(A_1) = zeta,
```

and symmetrically for `v`. Hence
`E[a 1(u, v in A_1)] >= E[a] - 2 zeta = 1 - eta - 2 zeta`, so
`val(U) >= val(x) >= 1 - eta - 2 zeta >= 1 - eta - 4 beta` by (3). This is
item (4).

## (5) Spectral form

Let `0 < mu(A) < 1` and `f = 1_A - mu(A)`, so `E_mu f = 0`. On a regular graph
with uniform `mu`, the normalized Laplacian has Rayleigh quotient
`E_(u,v)[(f_u - f_v)^2] / (2 E_mu[f^2])`, and

```text
E[(f_u - f_v)^2] = Pr[exactly one of u, v in A] = 2 mu(A) Phi_H(A),
E_mu[f^2] = mu(A)(1 - mu(A)),
```

so the quotient is `Phi_H(A)/(1 - mu(A))`. The variational principle gives
`lambda_2(H) <= Phi_H(A)/(1 - mu(A))`. With `A = A_0` and item (2),

```text
lambda_2(H) <= mu(A_0) Phi_H(A_0) / (mu(A_0) mu(P)) <= eta / (beta mu(P)).
```

This is item (5). (The same identity with `A = P` gives
`lambda_2(H) <= Phi_H(P)/(1 - mu(P)) = eta'/(beta mu(P))`, the same bound.)

## (6) The dichotomy and the trichotomy

Fix `beta_0 in (0,1)` and let `Phi_L(S) = eta <= eta_0`.

- If `beta <= beta_0`, item (4) gives `val(U) >= 1 - eta_0 - 4 beta_0`.
- If `beta > beta_0`, item (2) gives `mu(A_0) = beta > beta_0` and
  `Phi_H(A_0) <= eta / beta < eta_0 / beta_0`.

Taking `beta_0 = sqrt(eta_0)` gives (Y-lab)/(Y-cut) as stated, and
`1 - eta_0 - 4 sqrt(eta_0) >= 1 - 5 sqrt(eta_0)` because `eta_0 <= sqrt(eta_0)`.

For the trichotomy assume `beta > sqrt(eta_0)` and split on `mu(P) = 1 - beta`.

- `mu(P) >= 1/2`: item (5) gives
  `lambda_2 <= eta_0/(beta mu(P)) <= 2 sqrt(eta_0)`.
- `sqrt(eta_0)/2 <= mu(P) < 1/2`: item (5) with `A = P` gives
  `lambda_2 <= Phi_H(P)/(1 - mu(P)) <= 2 Phi_H(P) <= 2 eta_0/mu(P)
  <= 4 sqrt(eta_0)`.
- `mu(P) < sqrt(eta_0)/2`: this is (Y-thin).

## (7) Sharpness

- A labeling set `S_x = {(v, x(v))}` has `l == 1`, so `beta = zeta = 0` and
  `1 - Phi_L(S_x) = val(x)`: item (4) is an equality there.
- A cylinder `S = W x [q]` with `mu(W) = 1/q` has `l = q` on `W` and `0` off
  `W`, so `E[a] = q e(W) = 1 - Phi_H(W)` and `beta = 1 - 1/q`. Then
  `1 - eta - 4 beta < 0` for `q >= 5`, so item (4) is vacuous, as it must be:
  the value of `U` is unconstrained. This is the (Y-cut) branch, and it shows
  the branch is not removable.
- *Window form.* If `mu(S) = m/q` with `m in [1,10]` then `E l = m`,
  `1 - Phi_L(S) = E[a]/m`, `E[M] >= m(1 - eta)` and `E[X - M] <= 2 m eta`, so
  (1) becomes `E[l_u 1(v not in P)] <= m eta`, (2) becomes
  `mu(A_0) Phi_H(A_0) <= m eta` and (3) becomes
  `Pr[l_u != l_v] <= 2 m eta`, all still useful. But (4) becomes
  `val(x) >= m(1 - eta) - 2(m - mu(A_1))`, which is negative once `m > 2`. The
  `m`-fold labeling set `{(v, x_1(v)), ..., (v, x_m(v))}` is a genuine
  counterexample to a window version of (4) with `m` independent labelings of
  value `1/q` each and `1 - Phi_L(S) ~ 1/m`. So the theorem is stated at exact
  volume.

## Replay

`python3 experiments/sse-lift-base-gate-2026-09-18/check_load_rigidity.py 1`
checks (1), (2), (3), (4), `val(U) >= val(x)` on the exhaustive instances, the
Rayleigh identity `E[(f_u-f_v)^2]/(2 E[f^2]) = Phi_H(A)/(1 - mu(A))` for
`f = 1_A - mu(A)` (the step by which the consumer claim converts (Y-cut) into a
bound on `lambda_2`), the branch bound
`lambda_2(H) <= eta/(beta mu(P))`, and the dichotomy of (6) at
`beta_0 = sqrt(eta)`, all in exact rational arithmetic. Instance families: three
exhaustive `(|V|, d, q) = (6, 4, 3)` instances over all `C(18,6)` sets each,
planted labelings at noise `0, 1/20, 1/10, 1/5`, planted block bases (made
`d`-regular by degree-preserving cross-block rewirings) with cylinder witnesses,
and random or load-concentrated sets on
`(|V|, d, q) in {(24,4,4), (30,6,5), (40,4,8)}`. On seed 1 it checks 56,208 sets,
reports 0 failures and exits 0.

*Where regularity is used.* (0) needs `E_(u,v)[l_u] = E_mu[l]`, which is the
statement that the directed-edge law has marginal `mu`. An early version of the
replay added crossing edges without preserving degrees and item (1) failed on
those instances by exactly the degree defect, which is the expected behaviour:
for an irregular `H` the correct statement replaces `mu` by the degree measure
throughout.
