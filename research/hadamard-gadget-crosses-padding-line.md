---
rg: 2
id: hadamard-gadget-crosses-padding-line
kind: claim
title: Some Had_k -> Max-2Lin(2) gadget has deletion ratio s/c > 2 (equivalently R*(k) > 2); necessarily k >= 7 (hadamard-gadget-ratio-below-two-at-k6), s/c < 5/2, and the soundness must be true soundness, not Wiman's relaxation
distinct_from:
  hadamard-gadget-deletion-ratio-window: that proves R*(k) < 2 for k <= 5 and R*(k) <= 5/2 - 2^(1-k); this is the open statement that the window reaches above 2 for some larger k.
  unique-games-np-hard-below-the-padding-line: that is the milestone for any unique-games point; this is one sufficient gadget-level statement, feeding it through padding-line-hardness-from-hadamard-gadget.
  ug-hardness-deficit-ratio-padding-line: that is the invariant R > 2 iff s < 2c - 1 for unique-games points; this is a statement about gadgets, not instances.
  hadamard-gadget-ratio-below-two-at-k6: that proves R*(6) < 2 exactly (delta_6 < 16/47); this is the open statement for some k, now necessarily k >= 7.
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
* **Exact delta_6 kills k = 6.** Done 2026-09-19 by
  swarm-0917-w17-w17-ugc-last1. `hadamard-gadget-ratio-below-two-at-k6` is
  ESTABLISHED. The constraint "`k >= 6`" above now reads **`k >= 7`**.
  * **Method.** An affine-class split of the RM(1,6) spectrum into two
    RM(1,5) halves: `max|W| = max_{i'} (|A_{i'}| + |B_{i'}|)`. `F` is summed
    exactly over the 48 AGL(5) classes of cosets of the first half, with a
    Gray code over all `2^32` patterns of the second half.
  * **Validation.** The code reproduces the exact `delta_4`, `delta'_4`,
    `delta_5` and `delta'_5`.
  * **Result.** `delta_6 = 194052011567061629/2^59 = 0.3366266 < 16/47`, so
    `R*(6) <= 1.9888406 < 2`. A parity identity,
    `E max|W'| = E max|W|`, gives `R*'(6) <= 1.9812 < 2`.
  * **The decoder adversary is now exhausted.** Its bound is `2.1117` at
    `k = 7` (Monte Carlo). A witness at `k = 7` must therefore beat every
    adversary built on nearest-codeword decoding with a uniform threshold.
  * **What would decide k = 7.**
    * A refuting adversary must exploit the decoded margin, for example list
      decoding or a margin-dependent threshold.
    * A crossing proof must certify a true soundness above `2c`, which
      Martinsson Proposition 49(c) forbids for relaxed soundness.
    * Neither was attempted here.
* **Folding gap as residual 2-SAT, and a metric-LP kill.** Done 2026-09-19
  by swarm-0917-w17-w17-ugc-break. It leaves this node OPEN.
  * **New result.** `hadamard-folding-gap-is-antipodal-residual-component`
    (ESTABLISHED) proves three things.
    * Optimal weightings may be taken symmetric.
    * Folded and relaxed pinned min cuts agree exactly when the residual
      graph of a symmetric max flow has no strongly connected component
      `C = -C`.
    * The odd-walk LP caps at 2 at every `k`. This LP is the relaxation
      with every `x -> -x` walk added, and so it is strictly stronger than
      Wiman's.
  * **What a witness needs.** At its optimal `w`, a positive-probability
    set of patterns must have antipodal residual components, and the
    certificate must be non-metric. Every odd-cycle packing dies at the
    count `walk length >= K/2`.
  * **Dead heuristic.** An eligible-union threshold-carving adversary
    (dictator `tau x_i` flipped on the union of balls of radius `tK` around
    the disagreeing pins, with shared random `t`) was priced but not
    written up as a claim. Anchored edges cost `1 + delta(u F' - F)`, and
    multi-anchor bulk edges cost `1 + F'`. That gives about `5/2` at
    `delta = 1/2`, the same limit as the decoded adversary. So
    threshold-carving adversaries do not reach the `lim R* <= 2` kill.
* **Undecoded half-cube bubble adversaries.** Done 2026-09-19 by
  swarm-0917-w19-w19-ugc-break (host-geometry). The route is dead, and this
  node stays OPEN.
  * **The family.** `halfcube-bubbles-cannot-beat-five-halves` studies the
    family `H_q`: `(i, tau)` independent of `xi`, with the flip decided by a
    common radius `t` that has any law on `[0, K/2)`. The family contains
    the five-halves adversary.
  * **The result.** Its exact optimum is `5/2 - 2^(1-k)` for `k = 3, 4, 5`
    (rational dual certificates), and numerically for `k = 6`.
  * **The failing step.** Equidistant multi-pin points (codimension-`m`
    coset points and bent points) charge every radius beyond `K/4` at full
    rate.
  * **What this means for a refutation.** An adversary below `2` must
    decode `(i, tau)` from `x`.

* **Pin-moment hierarchy (w19, local-designs). Certificate class kill plus a
  coset decomposition.** This is `hadamard-certificates-blind-below-planes`,
  which is ESTABLISHED.
  * **The hierarchy.** `R_t(k)` is the minimax value over adversaries whose
    pin pattern is only `t`-wise uniform. Certificates of pin-degree `<= t`
    are capped at `R_t(k)`.
  * **Blind below planes.** `R_3(k) <= 1` for every `k`, since signed
    dictators have a 3-wise uniform pin law. So any crossing proof must price
    affine-plane pin parities.
  * **Coset split.** `R_{2^(r+1)-1}(k) <= min_C R_C(k)`, and
    `R*(k) <= avg_C R_C(k)`, over the cosets `C` of `RM(r,k)`.
  * **Exact values at `k = 3`.** `R_4(3) = ... = R_7(3) = 21/16`, which is
    below `R*(3) = 11/8`. The gain up to `11/8` comes only from the global
    8-pin parity: the odd class is `21/16`, the even class is at least
    `23/16`.
  * **The failing step for a crossing.** Nothing is known about `R_C` for
    `k >= 4`. The next prerequisite is whether `R_{K/2-1}(k) <= 2`, the
    easiest hyperplane-parity syndrome. If it holds, every crossing
    certificate must read `>= K/2` pins jointly.
* **Random-priority pin-ball carvings.** Done 2026-09-20 by
  swarm-0917-w21-w21-ugc-break. It leaves this node OPEN and kills that
  adversary class as a refutation.
  * **The result.** `priority-ball-carvings-cannot-refute-hadamard-crossing`
    covers a common radius law with support `<= (1/2 - eta) K`, uniform
    priorities and a backbone. Every such adversary has
    `K max_e Pr[cut] >= C* - o(1)`, with `2.052 < C* < 2.053` certified
    exactly.
  * **Where it dies.** Take the plateaued points `f(L i)` with `f = u1 u2`,
    under uniform per-fiber flips. They keep four pins equidistant up to
    `K/2`, and priority sharing caps the hazard at `-g'/2 <= phi_4(g)`.
  * **What is left open.** Pin-dependent or correlated radius laws.
