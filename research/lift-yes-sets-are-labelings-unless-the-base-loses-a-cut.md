---
rg: 2
id: lift-yes-sets-are-labelings-unless-the-base-loses-a-cut
kind: claim
title: Every set of measure 1/q in the label-extended graph of a q-label unique game with Phi_L(S) <= eta has support P with Pr[u in P, v not in P] <= eta and yields a labeling of value >= 1 - eta - 4 mu(V minus P), so a YES witness for Gap-SSE on a lift is either a near-optimal labeling or a sparse cut of the base
distinct_from:
  lifts-over-multiscale-expanders-expand-unless-ug-value-large: that controls the NO case (a lift of a low-value game over a multiscale-expanding base expands) and its necessity half only says 1 - Phi_L(1/q) >= max(val, 1 - Phi_H(1/q)); this is the converse at the YES case, turning an arbitrary non-expanding set of the lift into a labeling of almost the same value plus a cut of the base, with no hypothesis on the base at all.
  galois-unique-game-value-is-transversal-expansion: that identifies the value with expansion over transversals only; this handles sets that are not transversals and shows they are transversals up to the mass of the empty fibres.
  spectral-gap-ratio-reductions-cannot-prove-ugc: that is the unique-games spectral gate, which needs a YES instance of large value as input; this is the lemma that supplies that input from a small-set-expansion YES witness.
  low-label-threshold-rank-reductions-cannot-prove-ugc: that rounds a game of value 1-eps using the spectrum of the label-extended walk; this rounds a single set of the label-extended graph by integrality of its fibre loads, with no spectral input.
  spread-support-overlap-forces-non-expanding-small-sets: that manufactures non-expanding sets from an overlapping support map; this decodes a given non-expanding set of a lift and needs no support map.
  elementary-abelian-galois-games-round-with-linear-loss: that rounds an SDP certificate over F_p^N with loss O(eps log k); this rounds an integral set of an arbitrary lift with additive loss 4 mu(A_0) and no SDP.
artifacts:
  - experiments/sse-lift-base-gate-2026-09-18/check_load_rigidity.py
---

**ESTABLISHED.** Elementary and self-contained; the only inputs are
`a_uv <= min(l_u, l_v)` and the integrality of the fibre loads. Proof:
`lift-yes-set-load-rigidity-proof`. Exact replay over 56,208 sets (three
exhaustive `|V| = 6, q = 3` instances over all `C(18,6)` sets each, planted
labelings, planted block cylinders and random or load-concentrated sets on
`(|V|, d, q) in {(24,4,4), (30,6,5), (40,4,8)}`), 0 failures:
`experiments/sse-lift-base-gate-2026-09-18/check_load_rigidity.py`.

*Setting.* Exactly that of
`lifts-over-multiscale-expanders-expand-unless-ug-value-large`. `H` is a regular
multigraph on `V` with uniform `mu` and symmetric directed-edge law, `U` is a
unique game on `H` with permutations `pi_uv` of `[q]`, `pi_vu = pi_uv^-1`, and
`L = L(U)` is the label-extended graph on `V x [q]`. For `S <= V x [q]` of
measure `1/q`, so `|S| = |V|`:

```text
l_v = |S_v| in {0, ..., q},    E_mu l = 1,
a_uv = |{i in S_u : pi_uv(i) in S_v}|,     1 - Phi_L(S) = E_(u,v)[a_uv],
P = supp(S) = {v : l_v >= 1},   A_0 = V \ P,   A_1 = {v : l_v = 1},
beta = mu(A_0),   zeta = 1 - mu(A_1).
```

**Theorem.** Put `eta = Phi_L(S)`. Then:

1. *(Load-weighted escape.)* `E_(u,v)[l_u 1(v not in P)] <= eta`.
2. *(Support is nearly closed.)* `Pr[u in P, v not in P] = mu(P) Phi_H(P) =
   mu(A_0) Phi_H(A_0) <= eta`. In particular `Phi_H(A_0) <= eta / beta` and
   `Phi_H(P) <= eta / mu(P)`.
3. *(Load integrality and mass balance.)* `Pr_(u,v)[l_u != l_v] <= 2 eta`,
   `mu(A_0) >= mu({l >= 2})`, and `zeta <= 2 beta`.
4. *(Rounding.)* The canonical labeling `x` -- the unique element of `S_v` for
   `v in A_1`, arbitrary elsewhere -- satisfies
   `val(x) >= 1 - eta - 2 zeta >= 1 - eta - 4 beta`. Hence
   `val(U) >= 1 - eta - 4 mu(A_0)`.
5. *(Spectral form of (2).)* If `0 < beta < 1` then
   `lambda_2(H) <= Phi_H(A_0)/(1 - beta) = eta' / (beta mu(P))` with
   `eta' = mu(A_0) Phi_H(A_0) <= eta`, by the Rayleigh quotient of
   `1_(A_0) - beta`.

**Dichotomy.** For every `eta_0 > 0` and every `S` of measure `1/q` with
`Phi_L(S) <= eta_0`, at least one of:

- **(Y-lab)** `val(U) >= 1 - eta_0 - 4 sqrt(eta_0)`;
- **(Y-cut)** `H` has a set `A_0` with `mu(A_0) > sqrt(eta_0)` and
  `Phi_H(A_0) < sqrt(eta_0)`.

(Take `beta <= sqrt(eta_0)` or `beta > sqrt(eta_0)` in (4) and (2).) More
generally the threshold `sqrt(eta_0)` may be any `beta_0 in (0,1)`, giving
`val(U) >= 1 - eta_0 - 4 beta_0` or `mu(A_0) > beta_0` with
`Phi_H(A_0) < eta_0 / beta_0`.

**Spectral trichotomy.** Combining the dichotomy with (5), for every `S` of
measure `1/q` with `Phi_L(S) <= eta_0 <= 1`, at least one of:

- **(Y-lab)** `val(U) >= 1 - 5 sqrt(eta_0)`;
- **(Y-spec)** `lambda_2(H) <= 4 sqrt(eta_0)`;
- **(Y-thin)** `mu(supp S) < sqrt(eta_0)/2`.

Indeed, if `beta > sqrt(eta_0)` and `mu(P) >= 1/2` then
`lambda_2 <= eta_0/(beta mu(P)) <= 2 sqrt(eta_0)`; if `beta > sqrt(eta_0)` and
`sqrt(eta_0)/2 <= mu(P) < 1/2` then `lambda_2 <= Phi_H(P)/(1 - mu(P))
<= 2 eta_0/mu(P) <= 4 sqrt(eta_0)`.

**Sharpness.**

- (4) is tight up to the constant: a labeling set has `beta = 0` and
  `val(x) = 1 - eta` exactly.
- (Y-cut) cannot be dropped. If `W <= V` has `mu(W) = 1/q` then the cylinder
  `S = W x [q]` has measure `1/q`, `Phi_L(S) = Phi_H(W)` (the cylinder identity
  of `lifts-over-multiscale-expanders-expand-unless-ug-value-large`, item 3) and
  `beta = 1 - 1/q`, while `val(U)` may be as small as `1/q`. So a lift can carry
  a YES witness with no labeling behind it, but only by importing a
  non-expanding set of the base at the same density.
- The hypothesis `mu(S) = 1/q` exactly is used. For the weighted window
  `mu(S) in [delta, 10 delta]` with `delta = 1/q` the loads average
  `m = q mu(S) in [1, 10]`. Items (1) and (2) survive as
  `E[l_u 1(v not in P)] <= m eta` and `mu(A_0) Phi_H(A_0) <= m eta <= 10 eta`,
  and (3) as `Pr[l_u != l_v] <= 2 m eta`. Item (4) degrades to
  `val(x) >= m(1 - eta) - 2(m - mu(A_1))`, which is vacuous once `m > 2`, and
  it must be: the `m`-fold labeling set
  `{(v, x_1(v))} u ... u {(v, x_m(v))}` for `m` independent labelings of value
  `1/q` each has `1 - Phi_L(S) >= 1/m` while `val(U)` stays near `1/q`. So the
  rounding item is stated at exact volume, which is the form SSEH takes on
  regular graphs; (1), (2), (3) and (5) hold in the window with a factor `m`.

**Bearing.** The established necessity half of
`lifts-over-multiscale-expanders-expand-unless-ug-value-large` says a lift gains
no scale: `Phi_L(1/q) <= min(1 - val, Phi_H(1/q))`. This is the matching upper
bound on what a YES witness can be: up to an additive `4 mu(A_0)` the only
non-expanding sets of a lift at density `1/q` are the two families that
necessity already exhibits, labeling sets and base sets. A reduction that
outputs lifts therefore has exactly two ways to create its YES case, and (Y-cut)
is the case in which the lift is inert -- the hardness is already small-set
expansion hardness of the base at the same density `1/q`.

DERIVATION lift-yes-set-load-rigidity-proof
