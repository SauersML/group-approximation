---
rg: 2
id: fpbs-critical-dyadic-projection-estimate
kind: claim
title: Critical dyadic cluster-averaging projections have summable size-weighted operator norms
---

OPEN research hypothesis Q2 for every nonamenable Cayley graph. Q3 is a stronger optional estimate; neither is established.

## Attempts

* **Control the total projection using independent edge resampling.**
  `fpbs-bernoulli-projection-resolvent-bound` bounds Q=E P_omega in
  operator order by an explicit graph resolvent, giving ||Q||<1 at
  criticality. Each shell Q_N is below Q, but this supplies no
  size-weighted summability. The ghost derivative is precisely where
  the cluster-size factor returns; `fpbs-projection-resolvent-ghost-obstruction`
  refutes obtaining its upper bound by subtracting separate resolvent
  bounds. The universal shell estimate remains OPEN.

* **Prove it on trees and transport the proof.** `fpbs-regular-tree-dyadic-three-halves`
  gives `c_b N^(-3/2) <= ||Q_N|| <= C_b N^(-3/2)` on every regular tree of
  degree at least three, with an exact finite formula for the norm and an
  explicit limit for `N^(3/2)||Q_N||`; the size-weighted sum converges with
  room to spare. **Where it dies:** the proof combines the conditional
  cluster-size law along an open path, a branch generating-function
  coefficient bound, and radial sphere operator norms
  (`fpbs-tree-branching-radial-projection-proof`). All three are
  branching-specific. Nothing here survives on a Cayley graph without a tree
  structure, and the tree case recovers an already-known nonuniqueness class.
* **Derive it from invariance, nonamenability and finite clusters.** **Dead:**
  `fpbs-dead-invariant-cluster-dyadic-bound`, invalidated by
  `fpbs-fiid-finite-clusters-do-not-imply-dyadic-summability`. On the
  nonamenable graph `T_4 x Z` there is a group-equivariant factor of iid whose
  clusters are all finite, whose susceptibility is infinite, and whose
  size-shell operator norms satisfy `||Q_N||=P(N<=|C_o|<2N)` exactly, giving
  `sum_k 2^k ||Q_(2^k)|| >= E|C_o|/2 = infinity`. The heavy-tailed vertical
  intervals leave an amenable direction along which cluster averages have
  large operator norm, so a proof must use that all edges at a vertex share
  one independent retention law.
* **Bound the diagonal or a single root overlap.** The composition identity
  `<delta_o,Q_k^2 delta_o> = E[1{both in shell k} |C intersect C'|/(|C||C'|)]`
  is exact for independent root clusters. **Where it dies:** this is a trace
  moment and not an operator norm. Rare or highly aligned spectral directions
  are invisible to it, and any completed proof must control arbitrary test
  functions or high enough spectral moments.
* **Aim at the stronger geometric decay.** The variant
  `||Q_k|| <= C 2^(-(1+eta)k)` with `eta>0` would give summability
  immediately, and holds on trees with `eta=1/2`. It is unproved in general
  and is strictly stronger, so it inherits every obstruction above.
  **Correction (2026-09-17):** it is not strictly stronger. See the next item.
* **Equivalence with the critical l2 conjecture (swarm-0917, reframing).**
  `fpbs-critical-l2-equivalent-to-dyadic-projection-estimate` proves, on every
  transitive graph with finite critical clusters, Q2 <=> Q3 with `eta=1/2`
  <=> `||T_{p_c}||_(2->2)<infinity`. The new direction is a ghost-field
  tree-graph bound: a green vertex in `K_x` gives a third BK arm from the
  meeting point `z` on an `x`-`y` path, so entrywise
  `P(x<->y,|K_x|>=n) <= (e/(e-1)) M_(p_c,1/n) (T^2)(x,y)`. With a bounded `T`,
  the triangle condition holds, `M_h <= C sqrt h` (Barsky-Aizenman, imported by
  `fpbs-triangle-condition-gives-mean-field-magnetization`), and
  `||Q_k|| <= C||T||^2 2^(-3k/2)`, the tree exponent. **Where the approach
  class dies:** every approach to this hole proves Hutchcroft's l2 conjecture
  `fpbs-nonamenability-bounds-critical-connectivity-operator` on the same
  graph, and conversely that conjecture closes the hole
  (`fpbs-dyadic-estimate-from-critical-l2-route`). So the shell decomposition
  adds no independent failure point to `fpbs-universal-dyadic-route`. As a
  side result, Q2 and Q3 with `eta=1/2` hold on every graph in the known
  critical-l2 classes. The hole stays OPEN, exactly as open as the l2
  conjecture.
* **Split into a critical exponent half and a spectral half (2026-09-17,
  swarm-0917-w5-bs-dyadic, decomposition).**
  `fpbs-critical-l2-iff-volume-tail-and-spectral-spreading` proves the
  following, graph by graph on transitive graphs:
  * critical l2, and hence this hole (Q2 and Q3) on nonamenable Cayley
    graphs, is equivalent to (V) together with (S), where
    (V) is `P_{p_c}(|K|>=n) <= Cn^(-1/2)`, and
    (S) is `s(p)=1-iota(T_p) -> 0`, or equivalently
    `||T_p||_(2->2) = o(chi_p)`;
  * under (V), (S) follows from a single sequence with `s(p_n)` below an
    explicit threshold;
  * `s(p)=1` on every amenable graph;
  * on a Cayley graph, (S) forces `chi^H_p = o(chi_p)` for every amenable
    subgroup `H`.

  The proof inserts Hutchcroft's `gamma <= delta-1`
  (`fpbs-critical-volume-tail-gives-mean-field-susceptibility`) into his l2
  criterion (`fpbs-hutchcroft-l2-gap-criterion`). This replaces the
  class-specific susceptibility estimate used for acylindrically hyperbolic
  groups. The OPEN halves are
  `fpbs-critical-volume-tail-mean-field-universal` and
  `fpbs-normalized-two-point-spectral-radius-vanishes-universal`, joined by
  the route `fpbs-critical-l2-via-volume-tail-and-spectral-spreading`. Each
  half is necessary for the hole, so a counterexample to either refutes it.
  All the nonamenability sits in (S). The hole stays OPEN.
* **Continuity along per-generator weights from a known anchor.** **Dead:**
  `fpbs-dead-weighted-surface-continuity-l2`.
  * **Openness is free.** `fpbs-one-edge-sprinkling-l2-lipschitz` splits at the
    last sprinkled edge and applies BK, giving `T_{p'} <= T_p + T_{p'} R T_p`.
    So `1/||T||` is Lipschitz in the weight field, with constant `p` on fresh
    generators.
  * **Where it dies:** closedness needs a positive floor of `1/||T||` along the
    path. The floor always implies critical l2 at the endpoint, so it is never a
    weaker prerequisite (`fpbs-weighted-surface-continuity-reduces-to-uniform-floor`).
  * **Referee status (2026-09-17):** both claims are back to OPEN. All three
    referees refuted the "every path" equivalence in item 1: a path through a
    supercritical point has `inf phi = 0` but still ends at a certified point.
    The equivalence holds only for monotone paths. The `{a,t}` and `{b,t}`
    anchors are also untreated. The sprinkling lemma was checked as correct.
  * **What survives** is a one-step certificate needing an explicit anchor norm.
    The spherical-function tree anchor certifies `T_{2k} x Z` for `k >= 4`, but
    `F_2 x Z` only if `p_c(T_4 x Z) < 0.21085`.
  * **Consequence for this hole:** perturbative weight transport needs
    quantitative critical norm bounds at anchors, and qualitative theorems give
    none.
