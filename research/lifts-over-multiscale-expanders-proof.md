---
rg: 2
id: lifts-over-multiscale-expanders-proof
kind: route
title: Truncate loads at T, pay T^2 for light pairs through the random labeling, and integrate the heavy layers W_t against the base profile, with Markov for the lowest layers
target: lifts-over-multiscale-expanders-expand-unless-ug-value-large
requires: []
artifacts:
  - experiments/ugc-sse-reframe-2026-09-17/check_lift_rounding.py
---

Notation is that of the target claim. The only facts used about `H` are these:
the law of `(u,v)` is symmetric, its marginal is `mu`, and `e` is monotone
under inclusion. So (0)--(2) hold verbatim for reversible weighted chains with
`E_mu l = 1`.

## (0) Identities

`L` has stationary measure `mu(u)/q` and edge law `(u,i) -> (v, pi_uv(i))`, with
`(u,v)` a random edge and `i` uniform. For `S` of measure `1/q`,
`1 - Phi_L(S) = q E_(u,v)[a_uv] (1/q) / (1/q) = E[a_uv]`. Two properties follow:

- *Symmetry.* `a_vu = |{j in S_v : pi_uv^-1(j) in S_u}| = a_uv`.
- *Bound.* `a_uv <= min(l_u, l_v)`, because `pi_uv` is injective.
- *Loads.* `l_v <= q`, `E l = |S|/|V| = 1`, and by Markov `mu(B_T) <= 1/T`.

The random labeling `x(v)` is uniform on `S_v` (arbitrary if `S_v` is empty) and
independent across vertices. It satisfies `(u,v)` with probability
`Pr[pi_uv(x(u)) = x(v)] >= a_uv/(l_u l_v)` when `l_u, l_v > 0`. When
`a_uv = 0` the bound is trivial. So `val(U) >= R(S)`.

## (1) Master inequality

Split `a_uv` by whether both loads are at most `T`.

*Light pairs.* If `l_u, l_v <= T` and `a_uv > 0`, then
`a_uv <= T^2 a_uv/(l_u l_v)`. So the light part is at most `T^2 R(S)`.

*Heavy pairs.* `1(max(l_u,l_v) > T) <= 1(l_u > T) + 1(l_v > T)`. By symmetry of
the edge law and of `min`, the two terms have equal expectation. So the heavy
part is at most `2 E[min(l_u,l_v) 1(l_u > T)]`.

*Layer cake.* `min(l_u,l_v) = int_0^q 1(l_u >= t, l_v >= t) dt`, so
`E[min(l_u,l_v) 1(l_u > T)] = int_0^q Pr[u in B_T cap W_t, v in W_t] dt`.

- For `t <= T`: `B_T cap W_t = B_T`, and the integrand is
  `Pr[u in B_T, v in W_t]`.
- For `t > T`: `W_t <= B_T`, and the integrand is `Pr[u, v in W_t] = e(W_t)`.

Adding the light and heavy parts gives (1). (If `T >= q`, the second integral is
empty.)

## (2) Transfer

Assume `T >= 1/tau`.

- *Lowest layers, `t in [0, 1/tau]`.* Bound `Pr[u in B_T, v in W_t]` by
  `mu(B_T) <= 1/T`. The contribution is at most `1/(tau T)`.
- *Middle layers, `t in (1/tau, T]`.* `B_T <= W_t`, so
  `Pr[u in B_T, v in W_t] <= e(W_t)`.

Hence
`nu(S) <= T^2 R(S) + 2/(tau T) + 2 int_(1/tau)^q e(W_t) dt`. This is check (b)
of the script.

For `t >= 1/tau`, Markov gives `mu(W_t) <= 1/t <= tau`. So the profile applies:
`e(W_t) <= eta mu(W_t) + gamma`. Since `int_0^q mu(W_t) dt = E l = 1`,
`int_(1/tau)^q e(W_t) dt <= eta + gamma q`.

Take `T = 4/(tau nu)`, which is `>= 1/tau`. Then `2/(tau T) = nu/2`. If
`nu(S) >= nu` and `2 eta + 2 gamma q <= nu/4` (that is,
`8 eta + 8 gamma q <= nu`), then
`nu <= 16 R(S)/(tau^2 nu^2) + nu/2 + nu/4`.
So `R(S) >= nu^3 tau^2/64`, and `val(U) >= R(S)` by (0).

*Scale form.* Let `A` have `mu(A) < 1/q`. Add vertices one at a time until the
measure first reaches `1/q`. That gives `A' >= A` with
`mu(A') in [1/q, 1/q + 1/|V|] <= [1/q, 2/q] <= [1/q, tau]`. Monotonicity gives
`e(A) <= e(A') <= eta mu(A') <= 2 eta/q`. For `mu(A) in [1/q, tau]`,
`e(A) <= eta mu(A)` directly. So the profile holds with `gamma = 2 eta/q`, and
`8 eta + 8 gamma q = 24 eta <= nu`. Any `S` with `1 - Phi_L(S) >= nu` would force
`val >= nu^3 tau^2/64`. Contrapositively, `Phi_L(1/q) > 1 - nu`.

## (3) Necessity

- *Labeling sets.* For a labeling `x`, `S_x = {(v, x(v))}` has measure `1/q`
  and `a_uv = 1(pi_uv(x(u)) = x(v))`. So `1 - Phi_L(S_x)` is the fraction of
  satisfied edges. Maximizing over `x` gives `1 - Phi_L(1/q) >= val(U)`.
- *Cylinders.* For `W` with `mu(W) = 1/q`, `S = W x [q]` has measure `1/q`.
  `a_uv = q` when `u, v in W`, and `0` when `u` is not in `W` (since
  `S_u = emptyset`). If `u in W` and `v` is not in `W`, then `S_v = emptyset`
  and `a_uv = 0`. So `E a = q e(W) = e(W)/mu(W) = 1 - Phi_H(W)`.

*Sticky bases.* Suppose `H` has a c-sticky ladder of step `varsigma'`. The
exact-volume step (2) of `sticky-cylinder-gadget-compositions-kill-proof` gives
`T <= V` with `mu(T) = 1/q` and `1 - Phi_H(T) >= c - 2 varsigma' q`. The
cylinder over `T` then gives `Phi_L(1/q) <= 1 - c + 2 varsigma' q`.

## (4) Lift form

- *Completeness.* By the labeling-set identity, `val >= 1 - eps` gives
  `Phi_L(1/q) <= eps`.
- *Soundness.* This is the scale form of (2) with `eta = nu/24`.
- *Size.* `L` has `q|V|` vertices and is computed in polynomial time.

So NP-hardness of the stated Gap-UG problem on N2 bases yields NP-hardness of
Gap-SSE(`nu`, `1/q`), for every `nu`. That is `small-set-expansion-hypothesis`.

*Converse, by citation.* RST Theorem 3.2 gives, for every `q` and
`eps, gamma > 0`:

- completeness `1 - 2 eps - o(eps)`;
- soundness `O(q^(-eps/(2-eps))) + gamma`;
- NO profile `1 - Phi(S) <= 1 - Phi_(G(1-eps))(mu(S)) + gamma/mu(S)`.

Fix `nu` and choose the parameters in this order:

1. `eps` small, for completeness `>= 1 - nu`.
2. `tau` with `sup_(mu <= tau) (1 - Phi_(G(1-eps))(mu)) <= nu/48`, by the
   Gaussian fact cited in the claim.
3. `q` large and `gamma <= min(nu/(48 q), nu^3 tau^2/200)`, so that the
   soundness is `< nu^3 tau^2/64`.

For `mu(S) in [1/q, tau]` the profile then gives `1 - Phi(S) <= nu/24`.

*Weighted graphs.* RST's graphs are weighted, and for irregular graphs SSEH uses
sets of measure in `[delta, 10 delta]`. So let `E l = m in [1, 10]`, with
`1 - Phi_L(S) = E[a]/m`. The same computation applies with these changes:

- Markov gives `mu(B_T) <= m/T` and `mu(W_t) <= m/t`;
- the lowest layers run over `t in [0, m/tau]`;
- `int mu(W_t) dt = m`.

This yields
`m nu <= T^2 R + 2 m^2/(tau T) + 2 eta m + 2 gamma q`. Take `T = 4m/(tau nu)`,
and assume `8 eta + 8 gamma q <= nu`, which gives `2 eta m + 2 gamma q <= m nu/4`.
Then `R >= nu^3 tau^2/(64 m) >= nu^3 tau^2/640`. Replacing 64 by 640 in the
soundness threshold covers this case. The padding step needs vertex weights
`<= 1/q`.

## (5) Galois dictionary

In `Gal(G,K,mu)` the label-extended graph is `Cay(G,mu)` with fibres the cosets
of `K`, by `galois-unique-game-value-is-transversal-expansion`. The labeling
sets are the transversals, and the cylinders `W x [q]` are the unions of cosets.
(1)--(4) apply unchanged with `q = k`.

## Replay

`python3 experiments/ugc-sse-reframe-2026-09-17/check_lift_rounding.py 1` checks
the following in exact rationals:

- (1) and the displayed consequence of (2);
- `R <= val`;
- the labeling-set and cylinder lower bounds on `1 - Phi_L(1/q)`.

The exhaustive part covers four random 4-regular instances with `|V| = 6` and
`q = 3`, over all `C(18,6)` sets. The random part covers 1,200 sets on instances
with `(|V|, q)` in `{(24,4), (30,5), (40,8)}`, including concentrated loads. It
reports 0 failures and exits 0.
