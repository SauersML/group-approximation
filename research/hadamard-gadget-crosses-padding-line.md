---
rg: 2
id: hadamard-gadget-crosses-padding-line
kind: claim
title: Some Had_k -> Max-2Lin(2) gadget has deletion ratio s/c > 2 (equivalently R*(k) > 2); necessarily k >= 6, s/c < 5/2, and the soundness must be true soundness, not Wiman's relaxation
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
