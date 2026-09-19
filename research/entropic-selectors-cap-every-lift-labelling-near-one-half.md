---
rg: 2
id: entropic-selectors-cap-every-lift-labelling-near-one-half
kind: claim
title: For any random orientation of a 2-to-1 game, with high probability every labelling of the orientation lift, honest or not, has value at most half its game value plus half the mean history-conditional fiber bias plus a counting term of order sqrt(l/degree), so selectors that keep per-edge entropy lose half the game and beating one half forces sequential predictability
distinct_from:
  efficient-branch-selectors-list-decode-honest-outer-labels: that bounds honest and near-honest witnesses of polynomial-time selectors under NP not in RP; this bounds every labelling of the lift, with no honesty, efficiency or complexity assumption, but only for orientation laws that keep per-edge conditional entropy.
  view-local-branch-selectors-are-gauge-blind: that bounds witnesses from an equivariant menu of subexponential size for selectors with restricted views; this has no menu and no view restriction, and its invariant is the history-conditional bias of the orientation law instead of the selector's view.
  locally-read-witnesses-are-sound-on-planted-2to1-inputs: that bounds witness maps averaged over planted inputs for every orientation; this is per instance and bounds the maximum over all labellings, but only for high-entropy orientation laws.
  orientation-lifts-sandwich-2to1-game-values: that proves the floor val(G)/2 for every orientation; this proves the matching ceiling val(G)/2 + beta/2 + t for every orientation law of mean history bias beta, so for entropic laws the floor is the truth.
  bounded-rank-parity-selectors-pay-representation-weight: that bounds honest lift values of deterministic bounded-rank parity selectors on planted instances; this is silent about deterministic selectors and bounds all labellings of random ones on every instance.
artifacts:
  - experiments/entropic-selector-cap-2026-09-17/check_entropic_cap.py
---

**ESTABLISHED.** An unconditional class kill that reaches non-honest witnesses.
The proof is `entropic-selectors-cap-every-lift-labelling-near-one-half-proof`,
which is self-contained (Hoeffding's lemma is proved inline).

## Setting

* `G = (A, B, E, w, pi)` is a bipartite 2-to-1 game. The edges are
  `e_1, ..., e_M` with weights `w_i > 0` summing to 1. `|Sigma_A| = 2^l`,
  `|Sigma_B| = 2^(l-1)`, and each `pi_i : Sigma_A -> Sigma_B` is 2-to-1.
* An *orientation* `c` picks, for every edge `i` and fiber `t in Sigma_B`, one
  element `c_i(t)` of the fiber `pi_i^(-1)(t)`. Put `o_i(s) = 0` iff
  `s = c_i(pi_i(s))`. The *lift* `U_c` is the unique game with right alphabet
  `Sigma_B x {0,1}` (size `2^l`) in which a labelling `(sigma, tau)` satisfies
  edge `i = (a, b)` iff `tau_b = (pi_i(sigma_a), o_i(sigma_a))`. This is the
  orientation lift `U_o` of `orientation-lifts-sandwich-2to1-game-values`
  (its Setting), and every orientation in that sense is of this form.
* A *random orientation* is any joint law of `(c_1, ..., c_M)` on a probability
  space with a filtration `F_0 <= F_1 <= ... <= F_M`, where `c_i` is
  `F_i`-measurable. The edge order and the filtration are arbitrary. `F_0` may
  contain the instance, the selector's shared seed, an SDP solution, or anything
  else.
* The *history bias* of edge `i` is the `F_(i-1)`-measurable variable
  `beta_i = max_t | 2 Pr[c_i(t) = p_t | F_(i-1)] - 1 |`, where `p_t` is either
  element of the fiber `t` (both give the same value).
* `N = l (|A| + |B|)`, so that `U_c` has exactly `2^N` labellings.

## Statement

**Theorem.** For every `k >= 0`, with probability at least `1 - 2^(-k)` over
the orientation, every labelling `(sigma, tau)` of `U_c` satisfies

```text
val_(U_c)(sigma, tau)  <=  (1/2) val_G(sigma, tau')  +  (1/2) sum_i w_i beta_i  +  t,
t = sqrt( (N + k) ln 2 * (sum_i w_i^2) / 2 ),
```

where `tau'` is the first coordinate of `tau`. In particular,
`val(U_c) <= val(G)/2 + beta_bar/2 + t` with `beta_bar = sum_i w_i beta_i`.

For uniform weights on a biregular graph with degrees `D_A`, `D_B`:
`t^2 = (l ln 2 / 2)(1/D_A + 1/D_B) + k ln 2 / (2M)`.

**Two-sided sandwich.** Every orientation has `val(U_c) >= val(G)/2`
(item 1 of the sandwich). So for entropic laws (`beta_bar -> 0`,
`D_A, D_B >> l`) the lift value is `val(G)/2 +- o(1)` on every instance, for all
labellings at once.

**Tightness.** Take any deterministic orientation `f` that is consistent with a
best labelling `sigma*` of `G`, and flip each fiber bit independently with
probability `(1-delta)/2`. Then `beta_i = delta`. By the law of large numbers
`sigma*` keeps value `val(G)(1+delta)/2 - o(1)`, against the ceiling
`val(G)/2 + delta/2 + t`. At `val(G) -> 1` the ceiling is attained.

## Corollary (the class kill)

Let `S` be any selector, of any running time, that outputs a random
orientation. Suppose that with probability `theta > 2^(-k)` some labelling of
`U_c` has value `>= 1/2 + gamma`. Then, for every edge order and every
filtration, with probability `>= theta - 2^(-k)`,

```text
beta_bar = sum_i w_i beta_i  >=  2 (gamma - t),
```

so `E[beta_bar] >= 2 (gamma - t)(theta - 2^(-k))`.

**Invariant.** The mean history-conditional fiber bias `beta_bar`.

**Where every member dies.** At the union bound over the `2^N` labellings.
Azuma controls each fixed labelling up to `exp(-2 t^2 / sum w_i^2)`, and this
beats `2^N` once `t` exceeds the counting term. The only thing a labelling can
exploit is the part of the orientation that is predictable from the history.

**Killed (lift completeness `<= 1/2 + delta_bar/2 + t`, all witnesses).**

1. Fresh-coin and independent-rounding selectors. Shared data `Z` of any size
   (for example an SDP solution, a seed, or the whole instance) together with
   per-(edge, fiber) coins that are independent given `Z`, with
   `Pr[c_i(t) = p | Z]` within `delta_i/2` of `1/2`. Take `F_0 = sigma(Z)`.
   Soft rounding contributes nothing above `1/2`. Only the part of the rounding
   probabilities that is already biased by `2 gamma` counts.
2. Uniformly random and random-lexicographic orientations
   (`delta = 0`). This makes the first bullet of the target's `## Attempts`
   rigorous for all witnesses, not only balanced honest branches.

**Not killed (exact boundary).** With `F_0` trivial, the chain rule gives
`sum_i H(c_i(t_i) | F_(i-1)) <= H(c)`. The binary entropy satisfies
`h((1+beta)/2) >= 1 - beta` (concavity). So for uniform weights
`E[beta_bar] >= 1 - H(c)/M`. Any orientation of entropy `o(M)` therefore has
`beta_bar ~ 1`, and the cap is vacuous. This covers deterministic,
seeded, pseudorandom and gauge-randomised selectors (`n` gauge bits against
`M >> n` edges). The live cell H2
(`view-local-selectors-beat-one-half-through-non-honest-witnesses`) is
confined to orientation laws that are sequentially predictable. On a
`2(gamma - t)` mass of edges, in every exposure order, their fiber bits must be
determined by the history. Randomisation cannot help a selector past one half.
