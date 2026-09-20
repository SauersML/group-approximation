---
rg: 2
id: hastad-images-are-never-robustly-unique-proof
kind: route
title: Fourier-evaluate the Håstad test on an odd character chi of {sigma_W} ∪ Q, where Q is a projection-invisible even label set, then pigeonhole 2^(r0)+1 disjoint far near-solutions against the 2^(r0) coset points
target: hastad-images-are-never-robustly-unique
requires: []
artifacts:
  - experiments/ugc-hastad-ru-2026-09-17/check_hastad_invisible_sets.py
---

The notation is that of the target. For `T ⊆ SAT(W)` write
`chi_T(g) = prod over y in T of g(y)`.

## Step 1: acceptance of one modified table

Fix `W` and an odd set `T ⊆ SAT(W)`. Let `A_U = chi_({sigma_U})` (the
dictator) for every `U`, and let `B_W = chi_T`. Since `|T|` is odd,
`chi_T(-g) = -chi_T(g)`, so `B_W` is folded. It is a function on
`SAT(W)`-indexed tables, as required.

An equation of this `W` is accepted with probability `(1 + E[A_U(f) B_W(g) B_W(h)])/2`.
The characters are multiplicative and `chi_T(g)^2 = 1`, so

    A_U(f) chi_T(g) chi_T((f∘pi) g mu) = f(sigma_U) chi_T(f∘pi) chi_T(mu).

Next, `chi_T(f∘pi) = prod over y in T of f(pi(y)) = chi_(pi_2(T))(f)`.
Only the points of odd multiplicity in the image survive, because
`f(z)^2 = 1`. The three factors `f`, `mu` and `U` are independent given
`W`. `E_f[f(sigma_U) chi_R(f)] = 1[R = {sigma_U}]` for uniform `f`, and
`E[chi_T(mu)] = (1 - 2 eps)^|T|`. So the bias is

    beta_W(T) = (1 - 2 eps)^|T| Pr_(U|W)[pi_2(T) = {sigma_U}].        (1)

For `T = {sigma_W}` this is `1 - 2 eps`. Since `sigma` satisfies every
constraint, `pi(sigma_W) = sigma_U`. That is the honest value `1 - eps`.

## Step 2: the invisible modification

Let `T = {sigma_W} ∪ Q_W` with `Q_W` as in Theorem G. Then `|T| = |Q_W| + 1`
is odd. Multiplicities add mod 2, so `pi_2(T) = {sigma_U} Δ pi_2(Q_W)`
(symmetric difference), and `pi_2(T) = {sigma_U}` exactly when
`pi_2(Q_W) = ∅`. By (1),

    beta_W(T) >= (1 - 2 eps)^(M+1) (1 - theta).

The acceptance deficit against the honest table, per equation of this `W`, is

    (1/2)[(1 - 2 eps) - beta_W(T)]
      <= (1/2)[(1 - 2 eps) - (1 - 2 eps)^(M+1) + theta]
      <= (1/2)[2 M eps + theta] = Delta,

using `(1 - 2 eps) - (1 - 2 eps)^(M+1) <= 1 - (1 - 2 eps)^M <= 2 M eps`
and `(1 - 2 eps)^(M+1) <= 1`.

## Step 3: distance of one modified table

In every equation of `W`, the two `B`-slots are `B_W(g)` and `B_W(h)`. Each
of `g` and `h` is marginally uniform, because `h = (f∘pi) g mu` with `g`
uniform. So the `nu`-mass of the table `B_W` is `(2/3) q_W`, spread
uniformly over the functions `g`. Folding pairs `g` with `-g`, and both
characters below are odd, so the same computation holds over folded
representatives.

`chi_({sigma_W})` and `chi_T` differ at `g` iff `chi_(Q_W)(g) = -1`. Since
`Q_W` is nonempty, this happens for exactly half of all `g`. `chi_(Q_W)` is
even, hence constant on each pair `{g, -g}`, so it also happens for exactly
half of the representatives. Count slots with multiplicity. Each of the two
`B`-slots of an equation of `W` lands in the differing set with probability
`1/2`, so the tables are at `nu`-distance `(1/2)(2/3) q_W = q_W/3`.

*Repeated variables.* If `nu` counts each variable of an equation only once,
the degenerate equations need a correction. These are the equations with
`h in {g, -g}`, which is the same folded variable. That event depends only
on `(f, mu)`, so `g` stays uniform given it. On the event, the equation
contributes `1/2` instead of `1` to the expected differing slot count. So the
distance is at least `(1 - zeta_W/2) q_W/3`, where
`zeta_W = Pr[h in {±g} | W]`.

For a clean `W` in Corollary H, `pi : SAT(W) -> {±1}^U` is onto. Given `mu`
and a sign `c`, the event `f∘pi = c mu` fixes `f` on all `2^t` points, so
`zeta_W <= 2^(1 - 2^t) <= 1/2`.

## Step 4: proof of Theorem G

Let `a_0` be the honest assignment: `A_U = chi_({sigma_U})` and
`B_W = chi_({sigma_W})`. Let `a_i` agree with `a_0` except that
`B_W = chi_({sigma_W} ∪ Q_W)` for every `W` in `S_i`.

**Value.** An equation touches exactly one `B` table. So by Step 2,
`val(a_i) >= (1 - eps) - q(S_i) Delta >= 1 - eps - q_hi Delta`.

**Distance.** The sets `S_i` are disjoint. `a_i` and `a_j` differ exactly on
the tables `B_W` with `W in S_i ∪ S_j`. At each of those, one side is honest
and the other is modified, so by Step 3,
`dist_nu(a_i, a_j) >= (1 - zeta/2)(q(S_i) + q(S_j))/3 >= (2/3)(1 - zeta/2) q_lo`,
where `zeta = max zeta_W`. Under the multiplicity convention, `zeta = 0`.

**Pigeonhole.** Suppose RU held with some `x*` and `C`. Every `a_i` has value
`>= 1 - eps - gamma'/(4k)`, so it has a point `p_i in x* + C` with
`dist_nu(a_i, p_i) <= rho`. `|x* + C| <= 2^(r0) < N`, so `p_i = p_j` for
some `i != j`. The triangle inequality then gives
`dist_nu(a_i, a_j) <= 2 rho < (2/3)(1 - zeta/2) q_lo`, a contradiction. ∎

## Step 5: proof of Corollary H

Håstad's `W` is a `t`-tuple of independently uniform clauses of the
3SAT-5 formula `phi`, and `SAT(W)` is the set of assignments to its variables
that satisfy all `t` clauses. Call `W` *clean* if its `t` clauses have
pairwise disjoint variable sets. Each variable lies in at most 5 clauses, so
a fixed clause shares a variable with at most 13 others. Hence
`Pr[W not clean] <= C(t,2) · 13/|phi|`, which is `<= 1/2` once
`|phi| >= n_0 := 13 t^2`. Let `𝒲_0` be the clean `W`. Then `q(𝒲_0) >= 1/2`
and `q_max := max_W q_W -> 0` as `|phi|` grows.

**The sets `Q_W`.** Let `sigma` satisfy `phi`. For a clean `W`, pick `m` of
its clauses `c_1, ..., c_m`, where `m <= t`. A clause has 7 satisfying
assignments to its 3 variables, forming the cube `{±1}^3` minus one
vertex. Delete also `sigma|_(c_j)`. Two vertices of the cube touch at most 6
of its 12 edges, so an edge `{p_j, p'_j}` survives. These are satisfying
assignments of `c_j`, both different from `sigma|_(c_j)`, that differ in
exactly one variable `d_j`. Let

    Q_W = { y : y|_(c_j) in {p_j, p'_j} for j <= m, y = sigma elsewhere }.

Then `Q_W ⊆ SAT(W)`, `|Q_W| = 2^m = M` is even, and `sigma_W ∉ Q_W`.

**Invisibility.** `U` takes one uniform variable `u_j` of each clause, and
`pi` is restriction. By cleanness the image multiset is a product over the
blocks `j <= m`, with the other coordinates fixed. Block `j` contributes two
distinct points of multiplicity 1 if `u_j = d_j`. Otherwise it contributes
one point of multiplicity 2, since `p_j` and `p'_j` agree off `d_j`. A
product multiplicity is even as soon as one factor is 2. So
`pi_2(Q_W) = ∅` unless `u_j = d_j` for every `j`, and
`theta = 3^(-m)`.

**Parameters.** Take `m = ⌈log_3(2/gamma')⌉`, so that `theta/2 <= gamma'/4`.
With `eps <= gamma' 2^(-m-2)` we get `M eps <= gamma'/4`, hence
`Delta <= gamma'/2`. By Step 3, `zeta <= 2^(1 - 2^t) <= 1/2`.

Put `q_lo := 1/(4k(1 - zeta/2)) <= 1/(3k)`, and let `n` be large enough that
`q_max <= 1/(6k)`. Build `S_1, S_2, ...` greedily from `𝒲_0`. Add clean
`W` to `S_i` until `q(S_i) >= q_lo`. Then
`q(S_i) <= q_hi := q_lo + q_max <= 1/(2k)`.

Let `N = 2^(r0) + 1`. Since `k >= 2^(r0+1) + 1 = 2N - 1 >= 3`:

* the first `N - 1` sets use mass `<= (N-1)/(2k) < 1/4`;
* `q_lo <= 1/(3k) <= 1/9`.

This leaves `q(𝒲_0) - 1/4 > q_lo` for the `N`-th set, so the construction
does not run out.

Now check Theorem G:

* `q_hi Delta <= (1/(2k))(gamma'/2) = gamma'/(4k)`;
* `(2/3)(1 - zeta/2) q_lo = 1/(6k) > 2 rho` for every `rho < 1/(12k)`;
* `N > 2^(r0)`.

Theorem G therefore applies, for every satisfying `sigma`, `x*` and `C`.
Only one `sigma` is needed, and none of the argument looks at other
labellings. ∎

## Step 6: proof of Remark P

Let the new law be `omega' = s0 omega + (1 - s0) omega''`. Suppose each
assignment `a` of `H_eps` has a lift `a'` satisfying every
`omega''`-equation, and giving each source equation (of `omega`) the value
it has under `a`. A copy blow-up with consistency constraints is one example,
with all copies of `v` set to `a_v`.

Then `val_(omega')(a'_i) = 1 - s0(1 - val(a_i))`, and `dist_(nu')(a'_i, a'_j) >= s0 dist_nu(a_i, a_j)`.
The second holds because every source slot of `v` is a slot of a copy
carrying `a_v`.

Rerun Step 5 with `q_lo := 1/(4 k s0 (1 - zeta/2))` and
`q_max <= 1/(6 k s0)`. The loss is `s0 q_hi Delta <= gamma'/(4k)`. The
distance is `>= s0 (2/3)(1 - zeta/2) q_lo = 1/(6k)`. Once `k s0 >= 2^(r0+1) + 2 = 2N`, the `N` sets use source mass
`<= N/(2 k s0) <= 1/4`, and `q_lo <= 1/(3 k s0) <= 1/6`. Both fit inside
`q(𝒲_0) >= 1/2`. ∎
