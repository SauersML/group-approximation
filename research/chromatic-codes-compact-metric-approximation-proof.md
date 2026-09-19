---
rg: 2
id: chromatic-codes-compact-metric-approximation-proof
kind: route
title: Area bounds are metric-free and an eta-net of a compact group is a finite palette
target: chromatic-codes-kill-marks-in-compact-metric-approximations
requires: []
---

Self-contained. It uses no trace, no operator norm, no Property (T) and no
literature input.

## 0. Two facts about bi-invariant metrics

Let `(K, d)` be a group with a bi-invariant metric.

- **(B1) Conjugation is free.** `d(g u g^-1, 1) = d(u, 1)`. Also
  `d(uv, 1) <= d(u, 1) + d(v, 1)`, because
  `d(uv, 1) <= d(uv, v) + d(v, 1) = d(u, 1) + d(v, 1)`.
- **(B2) The commutator is 2-Lipschitz in each variable.** First,
  `d(u w u^-1 w^-1, u' w u'^-1 w^-1) = d(u w u^-1, u' w u'^-1)`. This is at most
  `d(u w u^-1, u' w u^-1) + d(u' w u^-1, u' w u'^-1) = d(u, u') + d(u^-1, u'^-1)`,
  which equals `2 d(u, u')`. The second variable is symmetric.

## 1. Area bounds survive in any bi-invariant metric

Let `rho : F(S) -> K` be any homomorphism of the free group. Put
`eps = max_(r in R) d(rho(r), 1)`. This is a maximum over the finite set `R`.

If `Area_R(w) <= A`, then `w = prod_(j <= A) g_j r_j^(+-1) g_j^-1` in `F(S)`.
By (B1), `d(rho(w), 1) <= A eps`. The conjugators `g_j` may be arbitrarily
long, and their length never enters.

## 2. The colouring

Let `pi : Gamma -> K_omega` be a homomorphism into a metric ultraproduct of
compact bi-invariant groups `(K_i, d_i)`. Suppose `pi(x) != 1`. Lift the
generators to get homomorphisms `rho_i : F(S) -> K_i`. Then:

- `eps_i = max_r d_i(rho_i(r), 1) -> 0` along `omega`;
- `delta_i = d_i(rho_i(x), 1)` has `omega`-limit `delta > 0`.

Choose `i` with `delta_i > delta/2` and `(A_Delta + A_0 + A) eps_i < delta/8`.
The set of such `i` is `omega`-large, so it is nonempty. For the corona
convention, infinitely many such `i` exist. Fix one such `i` and write
`d = d_i`, `rho = rho_i`.

Let `eta = delta/16`. By compactness, `K_i` is covered by finitely many sets
`P_1, ..., P_N` of `d`-diameter less than `eta`.

**CCC.** Colour each vertex `v` by the least `k` with `rho(c_v)` in `P_k`.
This uses finitely many colours and the graph has infinite chromatic number,
so some oriented edge `(v, w)` has `d(rho(c_v), rho(c_w)) < eta`. Then:

- `rho([c_v, h_v])` is within `A_Delta eps` of `rho(a_v) rho(x) rho(a_v)^-1`,
  by §1 and (B1). The latter is at distance `delta_i` from `1`, by (B1).
- `rho([c_w, h_v])` is within `A_0 eps` of `1`, by §1.
- `d(rho([c_v, h_v]), rho([c_w, h_v])) <= 2 eta`, by (B2).

So `delta_i <= A_Delta eps + 2 eta + A_0 eps < delta/8 + delta/8 = delta/4`.
This contradicts `delta_i > delta/2`.

**CDC.** Colour `v` by the cell of `rho(b_v)`. Some edge `(v, w)` has
`d(rho(b_v), rho(b_w)) < eta`, so `d(rho(b_v^-1 b_w), 1) < eta` by
bi-invariance. By §1, `rho(b_v^-1 b_w)` is within `A eps` of
`rho(a_vw) rho(x) rho(a_vw)^-1`, which is at distance `delta_i` from `1`. So
`delta_i < eta + A eps < delta/4`, again a contradiction.

Hence `pi(x) = 1` for every such `pi`, and so `x` lies in `Rad_C(Gamma)`.

## 3. The consequences

**Lifted T.** Let `N` be a normal subgroup of `T̄` and let `p : T̄ -> T` be the
projection, with kernel `<z>`.

- `p(N)` is normal in the simple group `T`.
- If `p(N) = 1`, then `N` lies in `<z>`.
- If `p(N) = T`, then `N<z> = T̄`, so `T̄/N` is a quotient of `<z>` and is
  abelian. Since `T̄` is perfect (`lifted-thompson-t-perfect-centre-cubically-elliptic`),
  `N = T̄`.

The mark of a code is non-central (`central-marks-escape-chromatic-codes`,
item 3), so `Rad_C(T̄) = T̄`. Every homomorphism from `T` to `K_omega`
composes with `p`, so it is trivial. `T` is infinite, so `T` embeds in no
`K_omega`. Taking `K_i` to be `U(n)` with the normalized HS norm, `Sym(n)`,
or finite bi-invariant groups gives that `T` is not hyperlinear, not sofic
and not weakly sofic. Subgroups of approximable groups are approximable, so
`V`, which contains `T`, is not hyperlinear either.

**Leavitt.** `Delta` is simple, so `Rad_C(Delta)`, which contains `z != 1`,
is all of `Delta`. The same argument gives that `Delta` is neither hyperlinear
nor weakly sofic. The target identifies `Delta` with `GL_20(R) = R^x`, so the
same holds for the binary Leavitt unit group.

## 4. Remark on the norm used by the criteria

Compactness of each `K_i` is essential: it gives the finite palette. The
operator norm is never used beyond this. Accordingly a target such as
`GL_n(C)` with the rank metric, which is not totally bounded, is not covered.
Nor is any non-compact `U(H)`. The `N_d(delta)` bound (CCC5) of the
operator-norm criterion is the covering number used here.
