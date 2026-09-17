---
rg: 2
id: spread-support-overlap-kill-proof
kind: route
title: Neighbouring views meet a p-biased atom set together with probability theta times the one-sided probability, and Efron--Stein with spread rho pins the zoom set to scale delta, so spread support overlap forces non-expanding sets
target: spread-support-overlap-forces-non-expanding-small-sets
requires: []
artifacts:
  - experiments/support-overlap-sse-kill-2026-09-17/check_support_overlap_kill.py
---

Notation is as in the target claim. `E` is a symmetric edge measure on `V x V`
with marginal `mu`, so `E(S, V) = mu(S)` and `1 - Phi(S) = E(S, S)/mu(S)`.
Write `q = 1 - p` and `g(s) = g_p(s) = 1 - q^s`.

## (0) Concavity

`g` is concave on `s >= 0` with `g(0) = 0`, so `g(theta s) >= theta g(s)` for
`theta in [0, 1]`. Also `g(s) = p sum_(j < s) q^j >= p s q^(s-1)` for integers `s >= 1`,
and the inequality is trivial at `s = 0`. Hence the pointwise overlap
`a(v,v') >= theta b(v)` gives `g(a(v,v')) >= theta g(b(v))` on each edge, since `g` is
increasing. Averaging over `E`, whose first marginal is `mu`, gives overlap `theta`.
For the one-sided version, fix `v`: the conditional edge mass with the pointwise
bound is `>= 1 - beta`, `g >= 0` elsewhere, so the conditional average of
`g(a)` is `>= (1 - beta) theta g(b(v))`. Average over `mu`.

## (1) Zoom inequality

`v in Z_X` iff `psi(v) n X != emptyset`, which has probability `g(b(v))`. So
`E B_X = sum_v mu(v) g(b(v)) = m(p)`. For an edge `(v, v')`, both endpoints
lie in `Z_X` whenever `psi(v) n psi(v') n X != emptyset`. That event has
probability `g(a(v, v'))`. So
`E A_X = sum_(v,v') E(v,v') P(v, v' in Z_X) >= E_E g(a) >= theta E_mu g(b) = theta m(p)`.

*Variance.* `B_X` is a function of the independent bits `1[x in X]`. The
Efron--Stein inequality gives
`Var B_X <= sum_(x in U) E[ p q (B_(X u {x}) - B_(X \ {x}))^2 ]`.
The increment `D_x = B_(X u x) - B_(X \ x)` is the `mu`-mass of vertices `v` with
`x in psi(v)` and `psi(v) n (X \ {x}) = emptyset`. So `0 <= D_x <= rho`, and
`D_x^2 <= rho D_x`. Moreover
`E D_x = sum_v mu(v) 1[x in psi(v)] q^(b(v) - 1)`, since `X \ {x}` misses the
other `b(v) - 1` atoms with that probability. Summing over `x`,
`sum_x p E D_x = E_mu[ p b q^(b-1) ] <= E_mu g(b) = m(p)` by (0). Hence
`Var B_X <= q rho sum_x p E D_x <= rho m(p)`.

## (2) Scale

Put `rho = rho(psi) <= delta`. The map `p -> m(p)` is continuous and increasing on
`[0, 1]`, with `m(0) = 0` and `m(1) = mu(psi) >= 3 delta`. Choose `p` with
`m(p) = 3 delta`. Then `Var B_X <= 3 rho delta` by (1). Let `I = [delta, 10 delta]`.

*Tails.* By Chebyshev, `P(B_X < delta) <= P(m - B_X > 2 delta) <= Var/(4 delta^2)`.
So `E[B_X 1(B_X < delta)] <= Var/(4 delta)`. On `B_X > 10 delta` we have
`B_X - m > 7 delta >= (7/3) m`, so `B_X < (10/7)(B_X - m)`. Also
`B_X - m > 7 delta`, so `B_X < (10/7)(B_X - m)^2/(7 delta)` there. So
`E[B_X 1(B_X > 10 delta)] <= (10/49) Var/delta`. Together,
`E[B_X 1(B_X notin I)] <= (1/4 + 10/49) Var/delta < 0.46 * 3 rho = 1.38 rho`.
So `E[B_X 1(B_X in I)] >= 3 delta - 1.38 rho >= 1.62 delta`.

*Selection.* Put `F_X = A_X - theta B_X`. By (1), `E F_X >= 0`. Since
`A_X <= B_X`, `F_X <= B_X`, so `E[F_X 1(B_X notin I)] <= 1.38 rho` and
`E[F_X 1(B_X in I)] >= -1.38 rho`. With `gamma = rho/delta`,
`E[(F_X + gamma B_X) 1(B_X in I)] >= -1.38 rho + (rho/delta)(1.62 delta) = 0.24 rho`.

If `rho > 0`, this is positive. Some `X` then has `B_X in I` and
`A_X >= (theta - rho/delta) B_X`, that is,
`mu(Z_X) in [delta, 10 delta]` and `1 - Phi(Z_X) >= theta - rho/delta`.

If `rho = 0`, then no atom lies in any `psi(v)` with `mu(v) > 0`. So `mu(psi) = 0`,
which contradicts `mu(psi) >= 3 delta > 0`.

## (3) Exact volume

Let the graph be regular of degree `d` on `n` vertices, and let `S = Z_X` from (2),
`s = delta n <= |S| <= 10 s`. Write `e(S,S)` for the number of ordered edge pairs
inside `S` (a loop counts once). Then `1 - Phi(S) = e(S,S)/(d |S|)`. Let `T` be a
uniform `s`-subset of `S`. A pair `u != v` of `S` lies in `T` with probability
`s(s-1)/(|S|(|S|-1)) >= s(s-1)/|S|^2`, and a loop with probability
`s/|S| >= s(s-1)/|S|^2`. So `E e(T,T) >= e(S,S) s(s-1)/|S|^2`, and
`E[1 - Phi(T)] = E e(T,T)/(d s) >= (1 - Phi(S)) (s-1)/|S| >= (1 - Phi(S))(s-1)/(10 s)`.
Some `T` attains at least the mean.

## (4) Closure

- *Tensoring.* The edge measure is `E tensor E_H` and `psi(v,h) = psi(v)`.
  Expectations of functions of `(v, v')` are unchanged, and
  `mu x mu_H{ (v,h) : x in psi(v) } = mu{ v : x in psi(v) }`.
- *Fibred pullback.* `(pi x pi)_* E' = E` means that expectations under `E'` of
  functions of `(pi v, pi v')` equal those under `E`. Taking `v' = V'` gives the
  same for `mu'` and `mu`. So overlap, spread and coverage transfer.
- *Mixtures.* `E_(alpha E + (1-alpha) E_Q) g(a) >= alpha E_E g(a)`, because `g >= 0`.
  The marginal is still `mu`.
- *Parallel repetition.* On an edge `(vbar, vbar')` of `E^(tensor r)`, each
  `(v_i, v'_i)` is an edge (in the support of `E`). With disjoint-union supports,
  `a = sum_i a(v_i, v'_i) >= theta sum_i b(v_i) = theta b`. The atom `(i, x)` lies in
  `psi(vbar)` iff `x in psi(v_i)`. The `i`-th marginal of `mu^(tensor r)` is `mu`,
  so the spread is unchanged.
- *Folding.* Let `Gamma` act on `V` with `psi o gamma = psi`. The quotient chain has
  edge measure `Ebar = (pi x pi)_* E` for the orbit map `pi`, and `psibar(pi v) = psi(v)`
  is well defined. Every quantity in the definitions (`g(a)`, `g(b)`, the spread
  masses, the coverage) is a function of `(psi(v), psi(v'))` or of `psi(v)`, so it
  has the same expectation under `Ebar`, `mubar` as under `E`, `mu`.

## (5) Instances

- *Grassmann.* If `dim(L n L') >= l - 1`, then
  `|L n L' \ {0}| >= q^(l-1) - 1 = theta (q^l - 1)`. A fixed nonzero `x` lies in
  a `(q^l - 1)/(q^n - 1)` fraction of `l`-subspaces, by transitivity of
  `GL_n(F_q)` on nonzero vectors and double counting. Labels and fibres do not
  change the subspace marginal. For `q = 2`,
  `(2^(l-1) - 1)/(2^l - 1) = 1/2 - 1/(2(2^l - 1)) >= 1/2 - 2^(-l)`, and
  `(2^l - 1)/(2^n - 1) <= 2^(l-n+1)`.
- *Agreement tests and view graphs.* In an agreement test, `a >= theta k = theta b`
  by definition. In a view graph, sharing a position gives `a >= 1 >= b/q`.
- *Projection games.* On the edge `(u, x)`, `a = 1`, `b(u) = |N(u)| <= k` and
  `b(x) = 1`. So `a >= b/k` from both ends. For the spread,
  `mu{ v : x in psi(v) } = mu(x) + mu(N(x))`, where `mu(u) = w_u/2W` and
  `mu(x) = sum_(u ~ x) w(u,x)/2W >= sum_(u ~ x) w_u/(k 2W) = mu(N(x))/k`.

## (6) Class kill

A NO instance of `Gap-SSE(eta, delta)` has `1 - Phi(S) < eta` for every `S` in the
relevant volume range. Items (2) and (3) exhibit a set with `1 - Phi >= theta - rho/delta`,
respectively `>= (theta - rho/delta)(s-1)/(10 s)`, and under the hypothesis this is `> eta`.
