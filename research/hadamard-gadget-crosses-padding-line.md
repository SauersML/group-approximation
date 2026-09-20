---
rg: 2
id: hadamard-gadget-crosses-padding-line
kind: claim
title: Some Had_k -> Max-2Lin(2) gadget has deletion ratio s/c > 2 (equivalently R*(k) > 2); necessarily k >= 7 (hadamard-gadget-ratio-is-below-two-at-k6), s/c < 5/2, and the soundness must be true soundness, not Wiman's relaxation
distinct_from:
  hadamard-gadget-deletion-ratio-window: that proves R*(k) < 2 for k <= 5 and R*(k) <= 5/2 - 2^(1-k); this is the open statement that the window reaches above 2 for some larger k.
  unique-games-np-hard-below-the-padding-line: that is the milestone for any unique-games point; this is one sufficient gadget-level statement, feeding it through padding-line-hardness-from-hadamard-gadget.
  ug-hardness-deficit-ratio-padding-line: that is the invariant R > 2 iff s < 2c - 1 for unique-games points; this is a statement about gadgets, not instances.
---

**OPEN.** For some `k >= 2` there is a `(c, s)`-gadget reducing Max-`Had_k`
to Max-2-Lin(2), in the sense of HHM+15 Definition 2.24, with `s/c > 2`.

* **Equivalent form.** By item 1 of `hadamard-gadget-deletion-ratio-window`,
  this says `R*(k) = K z*(P) > 2` for some `k`. In words: for some `k`, every
  folded distribution on `{-1,1}^(2^k)` that is random on the `2^k`
  characters cuts some length-one edge with probability greater than
  `2^(1-k)`.
* **Consequence.** Through the route `padding-line-hardness-from-hadamard-gadget`
  it gives `unique-games-np-hard-below-the-padding-line`, with `K = 2` labels.

## Constraints on any witness

These all follow from `hadamard-gadget-deletion-ratio-window`.

* **`k >= 6`.** Item 4 gives `R*(k) <= 1.8356` for `k <= 5`.
* **`s/c < 5/2`.** Item 2 gives `s/c <= 5/2 - 2^(1-k)`.
* **True soundness is required.** Item 5 (Martinsson, Proposition 49(c))
  shows that relaxed-soundness certificates cap at `2`.
* **Beat the decoded threshold adversary.** For every `(i, tau)` decoder with
  uniform conditional disagreement `delta`, the witness needs
  `1 + delta (3 - 4/K) > 2`, that is, `delta > 1/(3 - 4/K)`. The
  nearest-codeword decoder must therefore itself have `delta_k` above the
  threshold. This is only estimated, and not proved, for `k >= 7`:
  * `k = 6`: `delta_6 ~ 0.33663` against a threshold of `0.34043`. The
    adversary still wins numerically, which suggests `R*(6) < 2`.
  * `k = 7`: `delta_7 ~ 0.37446` against a threshold of `0.33684`. The
    adversary no longer rules out a crossing.
  * These Monte Carlo estimates are in
    `experiments/ugc-hadamard-gadget-window-2026-09-17/results-2026-09-18.txt`.

## Ways it can fail independently

* **A better adversary.** Find, for every `k`, a folded distribution random
  on `P` with maximum edge cut probability at most `2^(1-k)`. That refutes
  this node. Candidates:
  * list decoding;
  * a threshold `t` whose law depends on the decoded margin;
  * soft corrections that use several primaries at a time.
* **A limit argument.** Show that `lim R*(k) <= 2`, for example by an
  invariance or Gaussian argument on the `k -> infinity` limit of the
  minimax game. This would kill the whole Hadamard-gadget family as a route
  across the padding line.

## Attempts

* **Decoded threshold adversary with nearest-codeword decoding.** Kills
  `k <= 5` (2026-09-18, swarm-0917-w11-w11-ugc-break). It is inconclusive
  from `k = 7` on, because random words sit at normalized distance about
  `0.374` from `RM(1,7)`, above the threshold of about `0.337`.
* **Folding-gap decomposition and a k = 4 census.** Done 2026-09-19 by
  swarm-0917-w16-w16-ugc-break. It leaves this node OPEN, with a new
  necessary condition.
  * **The necessary condition.** `hadamard-crossing-needs-folding-gap` shows
    `R*(k) <= K z_U(k) + eta_k <= 2 + eta_k`. Here `z_U` is Wiman's relaxed
    value, capped at `2` by Martinsson Proposition 49(c), and `eta_k` is the
    largest edge mass inside the non-folded locus of an optimal relaxed
    adversary. So a witness at `k` needs `eta_k > R*(k) - 2`.
  * **The measured gap.** The folding gap is `0` at `k = 3`, where both sides
    are exactly `11/8`.
  * **The k = 4 window.** `hadamard-gadget-ratio-k4-sandwich` gives
    `1.45685 <= R*(4) <= 1.534727`. The upper bound is an exact rational
    mixture of folded adversaries and replaces `1.6583`.
  * **The failing step.** The gap is not known to be positive anywhere,
    because folded pricing is only heuristic. That question is
    `hadamard-gadget-k4-true-soundness-beats-wiman`.
  * **What this does not decide.** Nothing here moves `k >= 6`, since the
    `k = 5` census, with `2^31` variables, is out of reach for this code.
* **Monotonicity and threshold laws.** 2026-09-20, by
  swarm-0917-w23-w23-ugc-break (belief-breaker, finite-models). The node stays
  OPEN.
  * **Established: `hadamard-gadget-ratio-is-monotone-in-k`.** It proves
    `R*(k) <= R*(k+1)`. The diagonal restriction `g = f o iota`, with
    `iota(y)_(i,u) = y_i`, sends pins `chi_a` to `chi_(a,0)` and turns each
    edge into a 2-edge path. This node is therefore equivalent to
    `L = sup_k R*(k) > 2`, with `L` in `[1.45685, 5/2]`.
    * A witness at `k0` propagates to every `k >= k0`.
    * An upper bound at `k1` propagates to every `k <= k1`.
    * So the "limit argument" failure mode above is the only way to kill this
      node. No finite-`k` census can refute it.
  * **Killed class (continuum computation, not a separate node): radius-law
    decoded adversaries.** The class is the decoded
    threshold adversaries with any law `G` for the flip radius, taken inside
    the unique-anchor range (radius at most `K/4`).
    * The per-edge price is `(1-delta) + delta [G(a) + (a-1) g(a)]`. In the
      continuum this is `G - s G' <= C`, with `G(3/4) = 1` and `G(1) = 0`.
    * The extremal solution is linear, meaning the uniform threshold, with
      `C = 4`.
    * So no margin-dependent threshold law beats `1 + delta (3 - 4/K)`. The
      suggested candidate "a threshold `t` whose law depends on the decoded
      margin" is dead in that range.
    * Invariant: `G - s G'`. It dies at the boundary condition `G(3/4) = 1`.
    * Any improvement must use multi-anchor bubbles beyond radius `K/4`.
  * **Established: `hadamard-gadget-ratio-is-below-two-at-k6`, so `k = 6` is
    closed.**
    * Method: exact binomial moments `S_1..S_4` of the Walsh exceedance counts
      `N_t`, computed by a CRT integer computation over 5 joint-law types, and
      a moment-LP dual verified in rationals at every even threshold.
    * Result: `delta_6 <= 0.337997 < 16/47`, so `R*(6) <= 1.99287`. A witness
      now needs `k >= 7`, and the constraint "`k >= 6`" above becomes
      "`k >= 7`".
    * Also `R*(7) <= 2.13130` from 3 moments. This sharpens the `s/c < 5/2`
      constraint at `k = 7`.
    * Failed weaker versions:
      * 2 moments give `0.34751`;
      * 3 moments give `0.3458`;
      * both are above `16/47`.
  * **Where `k = 7` stands.** The decoded adversary cannot close it, because
    `delta_7 ~ 0.3745 > 32/95`. So the next kill needs a new adversary, beyond
    radius `K/4`, not better moments. Equivalently, it needs a proof of
    `L <= 2`.
