---
rg: 2
id: single-owner-radial-adversaries-stall-at-decoder-bound
kind: claim
title: Every single-owner radial label adversary for Had_k -> Max-2Lin(2) gadgets cuts some edge with K Pr[cut] >= 1 + delta_k(3 - 4/K), so the decoded threshold adversary is optimal in its class and the class cannot certify R*(k) < 2 for any k >= 7
distinct_from:
  hadamard-gadget-deletion-ratio-window: that proves the upper bound R*(k) <= 1 + delta_k(3 - 4/K) with one adversary; this proves the matching lower bound over the whole single-owner radial class, so no adversary in the class does better.
  hadamard-gadget-crosses-padding-line: that is the open statement R*(k) > 2 for some k; this does not decide it, and says only that any proof of R*(k) < 2 for k >= 7 must leave the class (hand-offs between codewords or non-radial labels).
artifacts:
  - experiments/ugc-hadamard-margin-adversary-2026-09-17/check_single_owner_dual.py
  - experiments/ugc-hadamard-margin-adversary-2026-09-17/radial_zone_lp.py
  - experiments/ugc-hadamard-margin-adversary-2026-09-17/geodesic_handoff_lp.py
  - experiments/ugc-hadamard-margin-adversary-2026-09-17/shifted_ball_continuum.py
  - experiments/ugc-hadamard-margin-adversary-2026-09-17/results-2026-09-19.txt
---

**ESTABLISHED.** Proof: `single-owner-radial-adversaries-stall-at-decoder-bound-proof`.

## Setting

The notation is that of `hadamard-gadget-deletion-ratio-window`. We have
`K = 2^k` and `P = {chi_a}`. The quantity `R*(k)` is `K min_A max_e Pr[A cuts e]`,
taken over distributions `A` that are folded and random on `P`. Write
`delta_k` for the mean normalized distance of a uniform word to `RM(1,k)`.

**The class Z (single-owner radial label adversaries).**

* **Randomness.** Draw `xi` uniform on `{-1,1}^P`. Draw `(i, tau)` jointly
  with `xi` in any way.
* **Zones.** The zone of a signed primary `y0 = s chi_p` is
  `{x : d(x, y0) < K/4}`. Distinct zones are disjoint and never adjacent.
* **Labels inside a zone.** Inside the zone of `y0`, set `A(x) = L_p(d(x, y0))(x)`.
  * `L_p(0), L_p(1), ...` is a random sequence of labels in `{C, -C, D, -D}`.
  * Here `C(x) = s xi_p` and `D(x) = tau x_i`.
  * The sequence may depend on all the randomness in any way.
  * It must satisfy `A(y0) = s xi_p`.
  * The same sequence is used at `-y0`, negated, so that `A` is folded.
* **Outside all zones,** `A(x) = tau x_i`.

**What Z contains.** In particular, the label may drop to `D` at a random radius.

* The decoded threshold adversary of item 3 of the window node is in Z.
* So is the five-halves adversary of item 2.

## Statement

For every `k >= 2` and every adversary in Z,

  `max_e K Pr[A cuts e] >= 1 + delta_k (3 - 4/K)`.

More precisely, zone `p` alone forces the value `1 + delta_p (3 - 4/K)`, where
`delta_p = Pr[xi_p != tau chi_p(i)]`. The average of `delta_p` over `p` is at
least `delta_k`.

## Consequences

* **The decoder adversary is optimal in Z.** Item 3 gives equality, so the
  optimum over Z is exactly `1 + delta_k (3 - 4/K)`.
* **For `k >= 7`, Z cannot certify `R*(k) < 2`.** Every adversary in Z costs
  at least `2.047`, because `delta_k >= 1/2 - sqrt((k+1) ln 2 / 2^(k+1)) >= 0.3528`.
  As `k` grows the class value tends to `5/2`.
* **Where an adversary proof for `k >= 7` has to go.** Any adversary proof of
  `R*(k) <= 2` for `k >= 7` must leave Z. It needs one of:
  * labels that are not radial within a zone;
  * direct hand-offs between codeword patches, since `C_p` and `C_q` are
    adjacent;
  * fallbacks other than a single dictator.
* **How the obstruction works.** The obstruction is a dual weight on the
  radial levels:

  `w_d = C / ((K-1-d)(K-2-d))`, with `C = (3K-4)(K-1)/K`.

  In the disagree branch, the label path must cross once from the class
  `{C, D}` to `{-C, -D}`. Under `w`, that crossing plus the remaining tail
  costs exactly `4 - 4/K`, wherever it happens.

## Numerical context (not part of the claim)

* **Radial LP.** `radial_zone_lp.py` solves the class-Z LP.
  * With `(i, tau)` independent of `xi` (`delta = 1/2`) it returns
    `5/2 - 2/K` for `K = 8` to `1024`.
  * For other `delta` it returns `1 + delta(3 - 4/K)`.
* **Geodesic hand-off LP.** `geodesic_handoff_lp.py` allows two codewords at
  distance `K/2` to hand off along a geodesic, with labels `C0`, `C1` and `D`.
  Its value is `1` for `K = 8` to `128`. So the midpoint obstruction that
  kills Z disappears once hand-offs are allowed.
* **Shifted-ball adversary.** `shifted_ball_continuum.py` explores one global
  hand-off adversary. It uses shifted balls with random radii and a `D`
  fallback. This is a heuristic search, not a bound.
  * The law that is optimal for the radial constraint blows up at crowded
    points. These are `N = 1/(1-2T)^2` codewords at normalized distance
    `T`, for example quadratic points.
  * Such a point costs `(N/2) f(T-)`, which is already `12.4` at `T = 0.36`.
  * So a working law needs `f(t) = O((1-2t)^2)` near the top of its support.
  * Whether some law gets below `2` is open. The numbers are in
    `results-2026-09-19.txt`.
