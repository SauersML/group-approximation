---
rg: 2
id: fpbs-pivotal-budget-universal
kind: claim
title: Every nonamenable Cayley graph has a uniform near-critical linear pivotal budget
---

OPEN research hypothesis P2. There exist graph-dependent C>0 and p0 in (pc,1) such that for all n>=1, all R>=n and all p in [pc,p0], E[N_piv | o connects to X_n inside B_R]<=Cn. No universal proof is supplied.

## Attempts

* **Charge the pivotal count to graph distance.** The hope is that `D_p(x,y)`,
  the conditional expected pivotal count, behaves like a metric so that a
  bound along a geodesic accumulates. **Dead:** `fpbs-pivotal-triangle-fails`.
  On the nonamenable Cayley graph of `C_6 * C_2` with `S={a,a^(-1),b}` the
  hexagon reliabilities give `D_2 - 2 D_1 = 6/209 > 0` at `p=1/2`, and an
  exact rational bound shows the defect stays positive at the critical
  parameter, which the branching calculation locates in `(0.513,0.514)`. The
  route `fpbs-dead-local-pivotal-charging` is killed by this.
* **Count bridges at criticality.** **Dead:**
  `fpbs-dead-bridge-count-at-criticality`. `fpbs-long-detours-with-no-bridges`
  gives a connected bridgeless model on `T_(2r) x Z` with divergent mean
  replacement-route length, and `fpbs-bridgeless-collective-fragility` shows
  its thinning threshold tends to one. A critical bridge count therefore
  controls neither the near-critical count nor resilience.
* **Prove it structurally and extend.** It holds with the optimal constant
  `1+exp(-2)` on every locally finite cactus, including in induced finite
  balls (`fpbs-cactus-pivotal-bound`,
  `fpbs-cactus-finite-ball-pivotal-budget`), and with constant `b` on graphs
  assembled from blocks of at most `b` edges. **Where it dies:**
  `fpbs-hierarchical-pivotal-amplification`. The recursive degree-three
  networks `J_k` have *adjacent* terminals, connection probability tending to
  about `0.992`, and conditional pivotal count growing like `0.0228 k` at the
  fixed parameter `p*=0.95841...`. Neither adjacency, bounded degree, nor rare
  conditioning bounds the count; the successful classes are exactly those with
  no multiscale cycle overlap, and a nonamenable nontransitive augmentation
  preserves the obstruction.
* **Ask for less.** Response 8 shows this pointwise hypothesis is stronger
  than the goal needs: `fpbs-integrated-pivotal-total-budget` already gives
  `M_(n,R)(1) -> -log rho` over the whole parameter interval, so only the
  *location* of the sensitivity is at issue. The work moved to
  `fpbs-pivotal-nonconcentration-universal` and
  `fpbs-integrated-sensitivity-universal`, which this claim implies and which
  are not known to be strictly weaker in any useful sense.
* **Assume the critical l2 gap.** On every Cayley graph a BK bubble, split at
  the connectivity operator by Cauchy–Schwarz, gives
  `E_p[N_(n,R)|E_(n,R)] <= 2 d ||T_p||_(2->2)^2` for all `n>=1` and `R>=n`
  (`fpbs-l2-gap-gives-bounded-pivotal-counts`). So the budget holds, with a
  count bounded independently of `n`, on every Cayley graph with
  `p_c<p_(2->2)` (`fpbs-l2-gap-cayley-graphs-satisfy-pivotal-kernels`). That
  class includes hyperbolic groups and the non-cactus products `T_k x Z^m`
  (`fpbs-pivotal-kernels-hold-on-known-gap-test-graphs`), but all of them
  already have `p_c<p_u`. **Where it dies:** the bound passes through a
  full-space bubble `W_n(p)` that is infinite at every uniqueness parameter,
  so a bound on it above `p_c` already certifies nonuniqueness. The
  finite-radius bubbles are finite but increase to `W_n`, so a universal proof
  must control the pivotal event uniformly over `R>=n` (Section 6 of
  `research/artifacts/fpbs/docs/pivotal-kernel-ordering-2026-09-12.md`).
