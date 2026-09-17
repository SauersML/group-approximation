---
rg: 2
id: fpbs-weighted-surface-continuity-reduces-to-uniform-floor
kind: claim
title: Continuity along per-generator weights has free openness, dies at a uniform floor equivalent to the endpoint, and one-step tree anchors certify T_2k x Z unconditionally for k >= 4
invalidates:
  - fpbs-dead-weighted-surface-continuity-l2
distinct_from:
  fpbs-one-edge-sprinkling-l2-lipschitz: that proves the sprinkling inequality and openness; this proves that openness is the only thing the continuity method adds, and calibrates the explicit anchor transfer.
  fpbs-l2-gap-class-closed-under-local-limits: that shows a gap passes to local limits only with common constants; this is the analogous obstruction inside one group along generator weights, where the missing common constant is a positive floor of 1/||T|| on a compact path.
  fpbs-gap-survives-product-generator-moves: that seeks threshold comparison under generator moves through the margin m(S); this shows that moving weights continuously transfers critical l2 only through an explicit anchor norm bound, and computes which explicit anchors suffice on T_2k x Z.
artifacts:
  - experiments/fpbs-sprinkling-anchor-2026-09-17/tree_anchor_threshold.py
  - experiments/fpbs-sprinkling-anchor-2026-09-17/output.txt
---

**OPEN.** Let `Gamma` be finitely generated and `U` finite symmetric.
Write `phi(q) = 1/||T_q||_{2->2}` for per-generator weights `q in [0,1)^U`.

1. **Openness is free, closedness is the target.** Let
   `gamma : [0,1] -> [0,1-eps]^U` be any continuous path from an anchor `gamma(0)`
   with `phi > 0` to the uniform critical point `gamma(1) = p_c(S) 1_S`. Then
   critical l2 at `gamma(1)` is equivalent to `inf_t phi(gamma(t)) > 0`.
   * The good set is always relatively open, by
     `fpbs-one-edge-sprinkling-l2-lipschitz`.
   * The residual closedness hypothesis is equivalent to the conclusion, for
     every path with that endpoint.
   * Hence no choice of anchor, path or critical surface turns the continuity
     method into a strictly weaker prerequisite. Its only possible content is an
     explicit anchor bound `phi(anchor) > Lipschitz cost of the path`, which is a
     one-step certificate from the fresh-generator form.
   * Qualitative anchor theorems give no such bound. These include the
     nonunimodular `T_k x Z^d` class, hyperbolic groups and the sphere-fibre
     criteria.
2. **Explicit tree anchor on `T_{2k} x Z = Cay(F_k x Z, standard)`.** Let
   `q = 2k-1`, `Xi(n) = (1 + n(q-1)/(q+1)) q^(-n/2)` and
   `Lambda_q(p) = sum_n |S_n| p^n Xi(n)`. Then `||T_p(T_{2k})|| <= Lambda_q(p)`, and
   `2 p Lambda_q(p) < 1` implies `p < p_{2->2}(T_{2k} x Z)`. The threshold `p*_k`
   solves `2 p Lambda_q(p) = 1`:

   | k | `p*_k` | walk counting `1/||A||` | `1/(deg-1) <= p_c` | `p_c(T_2k)` | `2pLambda` at `p_c(T_2k)` |
   |---|--------|--------|--------|--------|--------|
   | 2 | 0.21085 | 0.18301 | 0.20000 | 0.33333 | 3.317 |
   | 3 | 0.18194 | 0.15451 | 0.14286 | 0.20000 | 1.257 |
   | 4 | 0.16427 | 0.13715 | 0.11111 | 0.14286 | 0.723 |
   | 5 | 0.15180 | 0.12500 | 0.09091 | 0.11111 | 0.494 |

   * For `k >= 4`, `p_c(T_{2k} x Z) <= p_c(T_{2k}) < p*_k`, so critical l2 is
     certified unconditionally. Walk counting does not certify it from known
     bounds on `p_c`.
   * For `k = 2` (`F_2 x Z`), the tree anchor certifies critical l2 iff it
     proves `p_c(T_4 x Z) < 0.21085`. This is known qualitatively, but open as a
     number. Every other explicit proper anchor fails at every `p >= 1/5 <= p_c`:
     * the empty anchor: `p(2 sqrt3 + 2) > 1`;
     * the anchor `{t}`: `2 sqrt3 p > (1-p)/(1+p)`;
     * the anchor `{a}`: `4p > (1-p)/(1+p)`.
   * The one-step sprinkling certificate therefore does not yet reach the first
     case already covered by a qualitative theorem.

Proof: `fpbs-weighted-surface-continuity-reduces-to-uniform-floor-proof`.

## Attempts

1. **2026-09-17, refuted by all three referees.** Item 1 is false as stated.
   The proof shows only that `inf_t phi(gamma(t)) > 0` implies critical l2 at
   `gamma(1)`. For the converse it says only that "the continuity method has not
   succeeded", which proves nothing.
   * Counterexample: `F_4 x Z` with the standard generators. Run the path from
     `0` through a supercritical point (for example `0.5 * 1_S`, or
     `(1-eps) 1_S`), then back to `p_c 1_S`. At the supercritical point
     `tau >= theta^2 > 0`, so `phi = 0` and `inf phi = 0`. Yet item 2's `k = 4`
     tree-anchor certificate gives critical l2 at the endpoint.
   * The equivalence does hold for paths with `gamma(t) <= gamma(1)`
     coordinatewise, by monotonicity. It also holds in the form "critical l2
     holds iff some path has a positive floor". It is not proved for paths along
     the critical surface, which is the route's own sketch.
   * Secondary gap: "every other explicit proper anchor fails" treats only the
     empty, `{t}` and `{a}` anchors. The `Z^2` anchors `{a,t}` and `{b,t}` are
     never treated, and `output.txt` marks `{a,t}` inconclusive. One referee's
     oriented-percolation lower bound gives `chi_{Z^2}(1/5) >= 2.647`, so
     `2p chi > 1` and that anchor fails, but this is not in the files.
   * Checked and holding: the tree Schur test with `Xi`, the closed form of
     `Lambda_q`, the thresholds `p*_k`, the `k >= 4` certificate for
     `T_{2k} x Z`, and the failures of the empty, `{t}` and `{a}` anchors at
     `p >= 1/5`.
   * Repair: restrict item 1 to monotone paths, or to the existential form, and
     add the `{a,t}` and `{b,t}` anchors to the proof
     (`fpbs-uniform-floor-equivalence-restricted-to-monotone-paths`).
