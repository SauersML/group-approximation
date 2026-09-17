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
* **Transplant the budget from approximating groups (finite-models).**
  * *The route.* The operator form of the budget transplants along local or
    marked limits exactly when the connectivity norms admit one common bound
    `M` at one common margin `delta` above `p_c`.
    - `||T_p||` is lower semicontinuous under local convergence.
    - The uniform gap class `U_(M,delta)` is closed.
    - Limits of `U_(M,delta)` satisfy `p_c<p_u` and the budget with count
      `2dM^2` (`fpbs-l2-gap-class-closed-under-local-limits`).
  * *Where it dies.* Proposition 4.1 of
    `research/artifacts/fpbs-l2-gap-local-limits-2026-09-17.md`: for finite or
    amenable approximants, `limsup Gamma_M(G_k) <= p_c(G)` for every `M`.
    - On such graphs `||T_p|| >= chi_r(p)`.
    - `chi_r` is ball-local.
    - `chi_r(p) -> infinity` for every `p>p_c(G)`.
  * *What remains.* Surviving approximants must be quantitatively gapped.
    - Qualitative theorems such as Choi–Seo with Hutchcroft's criterion stop at
      the common-margin step.
    - Closed certificate classes, such as free products on union generating
      sets, reach only themselves.
  * *The direct budget transplant.* `E_p[N|E]` is ball-local, but PB begins
    at `p_c(G) <= liminf p_c(G_k)`. The approximants would need the budget
    below their own critical points.
* **Sum over walk lengths first (reframing, swarm-0917).**
  * *The kernel.* Summing (1.1) over `n<=R` gives
    `d/dp log A_R = E^tilt[N]/p`, where `A_R = sum_(n<=R) a_(n,R)` increases
    to `A(p) = sum_x g(x) tau_p(x)`. This is the expected number of visits of
    the walk to `C(e)`.
    - **GB** is a *bounded* Green-tilted pivotal count on `[p_c,p0]`.
    - **VIS** says `A(p)<infinity` for some `p>p_c`.
  * *Established* (`fpbs-green-visit-kernel-ordering`,
    `fpbs-green-visit-criterion-implies-nonuniqueness`, Section 3 of
    `research/artifacts/fpbs/docs/green-visit-kernel-2026-09-17.md`):
    - PB ⇒ GB ⇒ VIS ⇒ BS.
    - `p_c<p_(2->2)` ⇒ GB.
    - NC ⇒ VIS.
    - `tau_p in l2` ⇒ VIS.
    - `A(p_c) <= 1/(1-rho)`, and `A=infinity` at uniqueness.
  * *Consequence.* `fpbs-green-visit-criterion-universal` is the weakest
    kernel on the tip. A graph where VIS fails would refute this claim, IS,
    NC and the l2 gap there at once.
  * *Where it stops.* The pivotal content disappears.
    - GB and VIS have no pointwise-in-`n` control, so neither implies PB.
    - Like the bubble of Section 6, `A` is infinite at uniqueness, so VIS
      certifies nonuniqueness rather than deriving it.
    - RATE ⇒ VIS is not proved, and no converse is known.
* **Calibrate the bounded-count route on the tree (entropy-measure, swarm-0917 wave 5).**
  * *First idea, dropped.* Suppose a certificate sees the connection event only
    through three facts: it is increasing, it is supported on `E(B_R)`, and its
    probability is `P(E)`. Such a certificate cannot be uniform in `R`. Tribes
    events, the connection events of theta graphs, have probability at least
    `1-1/e` and conditional open-pivotal count at least
    `e^(-2) floor(log_(1/p)|E(B_R)|/2)`. This adds nothing new:
    `fpbs-hierarchical-pivotal-amplification` already defeats that class at
    bounded degree.
  * *Established* (`fpbs-tree-walk-pivotal-count-bounded-below-l2-threshold`).
    On `T_d` the random-walk count is the mean of `|X_n|` tilted by `p^k`. An
    `h`-transform of the radial chain by `(d-1)^(-k/2)` turns it into
    `sum k x^k sigma_k / sum x^k sigma_k`, where `x = p sqrt(d-1)` and
    `sigma_k <= d/(d-1)`. Ballot counts then show two regimes:
    - for `p<p_(2->2)=1/sqrt(d-1)` the count is bounded in `n`;
    - for `p_(2->2)<p<1` the count is at least `eps(p) n`, while
      `p_u=1`. The case `p=p_(2->2)` is not proved; numerically the count grows
      like `sqrt(n)`.
  * *Where it stops.* The n-free conclusion of
    `fpbs-l2-gap-gives-bounded-pivotal-counts` is sharp on `T_d`: it fails at
    every `p>p_(2->2)`, even though nothing happens to uniqueness there.
    - The budget is open only on graphs with `p_c=p_(2->2)`.
    - On such a graph, no method that proves n-free counts on `(p_c,p0]` can
      work unless that graph behaves unlike the tree. A proof must produce
      genuinely linear counts.
    - The tree does not refute PB, which holds on `T_d` with `C=1`. It gives
      no transitive example where counts beat `n`.
