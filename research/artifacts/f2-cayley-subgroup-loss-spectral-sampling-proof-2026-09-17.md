# Sample characters from the spectral measure of S until they span a c-dimensional V; the subspace mass bound mu(V) <= |V| 2^-c bounds the stopping time by E_c, and Wald's identity bounds Pr[a not in V^perp] by E_c d_S(a)/2

*Attempt artifact (2026-09-17, wave `swarm-0917`), formerly route
`f2-cayley-subgroup-loss-spectral-sampling-proof` into
`f2-cayley-subgroup-sets-lose-at-most-log-inverse-density`, `requires: []`,
artifact `experiments/sse-small-instances-2026-09-17/run_census.py`. Demoted from
the graph because the referee stage of this lane produced no verdicts: the result
was written as ESTABLISHED but no referee vote was recorded for it, so it lands
agent-written only, not agent-verified. **No referee refuted it** — no referee
read it. Nothing below is known to be wrong, and part F of `run_census.py` checks
its three steps numerically in exact rational arithmetic. Restore it as a route
once a full referee pass survives.*

Notation is as in the target claim: `N = 2^k`, `|S| = s = 2^(k-c)`,
`d_S(a) = |S \ (S+a)|/s`, and `E_c = sum_(i=1)^c 1/(1 - 2^(-i))`.

## (0) Spectral measure

Put `f = 1_S` and `f^(y) = N^(-1) sum_x f(x) (-1)^(x.y)`. Parseval gives
`sum_y f^(y)^2 = s/N`, so `mu(y) = N f^(y)^2 / s` is a probability measure on
`F_2^k`.

## (1) Displacement is a character probability

```text
|S n (S+a)| = sum_x f(x) f(x+a) = N sum_y f^(y)^2 (-1)^(a.y).
```

Dividing by `s` gives `1 - d_S(a) = sum_y mu(y) (-1)^(a.y) = 1 - 2 Pr_(y~mu)[a.y = 1]`,
so `d_S(a) = 2 Pr_mu[a.y = 1]`.

## (2) Subspace mass bound

For a subspace `V`,

```text
sum_(y in V) f^(y)^2 = N^(-2) sum_(x, x' in S) sum_(y in V) (-1)^((x+x').y)
                     = N^(-2) |V| #{(x, x') in S^2 : x + x' in V^perp}
                     = N^(-2) |V| sum_(cosets C of V^perp) |S n C|^2
                     <= N^(-2) |V| s^2.
```

So `mu(V) <= |V| s / N = |V| 2^(-c)`.

## (3) The sampled subgroup and its stopping time

Draw `y_1, y_2, ...` iid from `mu`. Put `V_0 = {0}`,
`V_t = span(y_1, ..., y_t)` and `T = min{t : dim V_t = c}`. The dimension grows
by at most one per step. While `dim V_(t-1) = j < c`, the step raises it with
probability `1 - mu(V_(t-1)) >= 1 - 2^(j-c) >= 1/2`, by (2). So the waiting time
at dimension `j` is stochastically dominated by a geometric variable with mean
`1/(1 - 2^(j-c))`. Summing over `j = 0, ..., c-1`:

```text
E T <= sum_(j=0)^(c-1) 1/(1 - 2^(j-c)) = E_c = c + sum_(i=1)^c 1/(2^i - 1) <= c + 1.607.
```

In particular `T < infinity` almost surely. Put `H = V_T^perp`, a subgroup with
`|H| = N / 2^c = s`. Let `p` be its law.

## (4) Wald's identity

`a not in H` iff some `v in V_T` has `a.v = 1`. Since `V_T` is spanned by
`y_1, ..., y_T` and `v -> a.v` is linear, this happens iff some `t <= T` has
`a.y_t = 1`. Put `X = sum_(t <= T) 1[a.y_t = 1]`. The event `{T >= t}` depends only
on `y_1, ..., y_(t-1)`, so it is independent of `y_t`. Therefore

```text
Pr_p[a not in H] <= E X = sum_t Pr[T >= t] Pr_mu[a.y = 1] = E T d_S(a)/2 <= (E_c/2) d_S(a).
```

This is item 1 of the target. When `d_S(a) = 0` it forces `Pr_p[a not in H] = 0`,
so `C(S)` is well defined, with the convention that such `a` impose
`Pr_p[a not in H] = 0`.

## (5) Transfer to every weight law

For any `w`,
`E_p Phi(H) = W^(-1) sum_a w_a Pr_p[a not in H] <= (E_c/2) W^(-1) sum_a w_a d_S(a) = (E_c/2) Phi(S)`.
Some `H` in the support of `p` is at most the mean. The same computation with an
optimal `p` for `C(S)` gives `min_H Phi(H) <= C(S) Phi(S)`.

*Duality.* Fix `C' < C(S)`. Consider the zero-sum game in which one player picks
`H` (pure strategies: the subgroups of size `s`) and the other picks
`a != 0`, with payoff `1[a not in H] - C' d_S(a)`. By definition of `C(S)`, every
mixed `p` has some `a` with positive payoff, so the value is positive. Von
Neumann's minimax theorem then gives a mixed `w` with
`min_H sum_a w_a (1[a not in H] - C' d_S(a)) > 0`, that is
`min_H Phi_w(H) > C' Phi_w(S)`. If `Phi_w(S) = 0`, then (4) forces
`Pr_p[a not in H] = 0` on the support of `w`, so `min_H Phi_w(H) = 0`, a
contradiction. So `sup_w min_H Phi_w(H)/Phi_w(S) >= C'`, and together with the
first half this is equality. This is item 2.

## (6) Algorithm

The subgroups of index `2^c` are the `V^perp` with `dim V = c`. They are
enumerated through reduced row echelon `c x k` matrices, and there are at most
`4 * 2^(c(k-c)) <= 4 N^c` of them. `w(H)` costs `O(N c)`. Accept iff some `H`
has `w(F_2^k \ H) <= (E_c/2) eta W`.

- *YES* (`Phi_G(2^-c) <= eta`): some `S` with `|S| = s` has `Phi(S) <= eta`. By (5)
  some `H` has `Phi(H) <= (E_c/2) eta`, so the algorithm accepts.
- *NO* (`Phi_G(2^-c) >= 1 - eta`): every set of size `s`, including every `H`, has
  `Phi(H) >= 1 - eta > (E_c/2) eta`, so the algorithm rejects.

The time is `N^(c + 1) poly(k)`. This is item 3, since
`(E_c/2) eta < 1 - eta` holds whenever `eta (c + 3.61) < 2`.

## (7) Half measure

`E_1 = 2`, so `c = 1` gives factor `1`. `Phi_G(1/2)` equals
`min_(y != 0) w{a : a.y = 1}/W = (1 - lambda_2)/2`, which matches the classical
lower bound `Phi(S) >= (1 - lambda_2)(1 - mu(S))`. This is item 4.

## Replay

`run_census.py F` checks (1), (2) and the conclusion of (4) in exact rational
arithmetic:
- (1) and (2) on random sets for `(k, s)` in
  `{(3,4), (4,2), (4,4), (4,8), (5,4), (5,8)}`;
- the exact law of the stopped process (a memoised Markov chain over subspaces),
  against `E_c d_S(a)/2`, for `k <= 4`;
- `C(S) <= E_c/2` by linear programming on the same sets and on the extremal
  witnesses of part E.
