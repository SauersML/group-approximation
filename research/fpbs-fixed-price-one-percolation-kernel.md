---
rg: 2
id: fpbs-fixed-price-one-percolation-kernel
kind: claim
title: Every Cayley graph of a nonamenable fixed-price-one group has strict percolation thresholds
---

**OPEN.** For every nonamenable finitely generated group Gamma of fixed price one and every finite symmetric generating set S, prove p_c(Cay(Gamma,S))<p_u(Cay(Gamma,S)). No proof route establishing this claim is supplied. The quantitative cost bound becomes 0<=0 under threshold equality and cannot close it.

## Attempts

* **Push the quantitative cost bound.** Response 1
  (`research/artifacts/fpbs/fixed-price-percolation.md`) proves
  `C^*(Gamma)-1 <= (d/2)(p_u-p_c) - (kappa(p_c)-kappa(p_u))`, where `kappa(p)`
  is the finite-cluster density `E_p[1/|K_p(o)|]`, and this is sharp on
  regular Cayley trees. **Where it dies:** under threshold equality every term
  on the right vanishes and the inequality reads `0 <= 0`. The bound runs the
  productive way only as `fpbs-threshold-collapse-forces-price-one`, collapse
  implies maximal cost one, which is exactly why it cannot exclude collapse
  inside the cost-one class. Lyons' theorem
  (`fpbs-non-fixed-price-one-has-nonuniqueness`) has the same direction; no
  mechanism is known for the converse.
* **Use fixed price one as a hypothesis.** **Where it dies:** no attack in the
  archive does. Every other route into `fpbs-benjamini-schramm-universal` --
  the pivotal budget, the integrated and exponential sensitivity targets, the
  dyadic projections, the connectivity operator -- quantifies over all
  nonamenable Cayley graphs and never mentions cost. Establishing any of them
  would settle this kernel as a special case rather than by using its
  hypothesis, so it currently carries no usable extra structure.
* **Convert a cheap graphing into percolation geometry.** A low-cost graphing
  or an FIID sparse spine (`fpbs-sparse-spine-cost-bound`) is an invariant
  subgraph of small expected degree, which is tempting to compare with a
  near-critical cluster. **Dead:** `fpbs-cost-one-routes-cannot-be-uniformly-tight`
  and `fpbs-quantitative-routing-tail-bound` show that nonamenability forces
  the routes in such subgraphs to be long and not uniformly tight, killing
  `fpbs-dead-uniform-tight-routes-contradiction`. Cheapness gives no control
  on the geometry that thresholds depend on.
* **Argue only from Bernoulli facts at `p <= p_c` plus soft supercritical
  properties.** These are invariance, ergodicity, insertion tolerance,
  monotonicity, uniqueness above `p_c` and continuity of `theta`.
  **Would be dead on a large part of this kernel** (swarm-0917,
  obstruction-miner; pending referee): the drafted proof of the open claim
  `fpbs-soft-collapse-on-fg-normal-and-kazhdan-groups` builds invariant sparse
  spines on every Cayley graph of two classes of groups:
  - every group with an infinite finitely generated normal subgroup `N` of
    infinite index, and every group commensurable with one. The construction
    uses iid Bernoulli sheets over `Gamma/N`, joined by rare random-walk
    excursions whose projected law is the same from every point of a coset;
  - every infinite Kazhdan group, through the unique infinite cluster of the
    Hutchcroft--Pete maximal-frequency graph, of density at most `p`.

  By Theorem A of `fpbs-soft-collapse-iff-invariant-sparse-spines`, each such
  graph carries a family equal to Bernoulli through `p_c` that satisfies
  (S1)--(S4) and has a unique infinite cluster for every `t > p_c`.
  **Invariant:** existence of invariant sparse spines. **Step where every member
  dies:** the continuation from `p_c` to `p_c + eps`.

  This holds regardless of fixed price, so on Kazhdan groups the obstruction
  does not wait for the open fixed-price-one question. The fixed-price-one
  hypothesis gives soft arguments nothing on these classes, which include
  `H x K`, surface-by-surface groups, braid groups, `SL_n(Z)` with `n >= 3`,
  lattices in `Sp(n,1)`, and torsion Kazhdan groups.

  What survives: nonamenable groups without (T) and not commensurable with a
  group having such an `N`. The named test cases are single torsion Tarski
  monsters, torsion-free Tarski monsters with trivial centre, `B(m,n)`,
  `Z/2 wr F_2` and `BS(2,3)`. There, whether soft arguments can work is exactly
  whether invariant sparse spines exist.
* **Soft arguments on wreath products and split extensions.** **Dead**
  (swarm-0917, inverter; agent-verified only, no referee yet). The claim
  `fpbs-soft-collapse-on-wreath-and-split-extensions` proves a coset bypass
  criterion. Take an infinite finitely generated `K <= Gamma`, a finite set
  `Sigma_1` and an infinite set `Y`, such that
  - `x^{-1} y x in K Sigma_1 K` for all but finitely many `y in Y`, for every
    `x`, and
  - `Y ∩ g p K p^{-1}` is finite for all `g, p`.

  Then iid Bernoulli(`eps`) selection of left cosets of `K`, with the cosets
  joined through infinitely many disjoint conjugated bypasses, gives
  invariant sparse spines on every Cayley graph. The proof needs only Theorem A.

  This applies to every permutational wreath product `A wr_X Q` with `Q`
  infinite and an infinite orbit, taking `K = Q` and `Y` a lamp orbit. It
  also applies to split extensions `N ⋊ K` with an element of finite
  `N`-class and infinite `K`-orbit.

  **Invariant:** existence of invariant sparse spines. **Step where every
  member dies:** `p_c -> p_c + eps`.

  This kills the survivor `Z/2 wr F_2`, and also `Z wr F_2`, `F_2 wr Z` and
  `F_2 wr F_2`. The mechanism is disjoint from the normal-subgroup one: the
  criterion never applies with a commensurated `K`. Remaining survivors:
  `BS(2,3)` (here `<a>` is commensurated), torsion Tarski monsters (no
  infinite `K` of infinite index), torsion-free Tarski monsters, and `B(m,n)`.
* **Soft arguments over subgroups with infinite conjugate intersections
  (2026-09-17).** **Dead** (swarm-0917, inverter; agent-verified only, no
  referee yet). The claim
  `fpbs-soft-collapse-over-conjugate-intersection-subgroups` proves the
  following. Suppose `H <= Gamma` is infinite, finitely generated and of
  infinite index, and every finite intersection of conjugates of `H` is
  infinite (condition (C); it holds for every commensurated `H`). Then iid
  Bernoulli(`eps`) selection of left cosets of `H`, with sheets joined by
  random-walk excursions, gives invariant sparse spines on every Cayley graph.
  The proof needs only Theorem A.

  The new step: excursions launched from `z h` with
  `h in H ∩ v_1 H v_1^{-1} ∩ ... ∩ v_d H v_d^{-1}` follow the same coset
  itinerary as from `z`, and (C) makes these launch points infinite, so
  Borel--Cantelli applies without normality.

  **Invariant:** existence of invariant sparse spines. **Step where every
  member dies:** `p_c -> p_c + eps`.

  This kills the survivor `BS(2,3)`, and also every nonamenable `BS(m,n)`,
  `SL_2(Z[1/p])` (via `SL_2(Z)`; this group lacks (T), and by Margulis'
  normal subgroup theorem it has no infinite normal subgroup of infinite
  index) and nonamenable graphs of groups with finite-index edge groups.
  It recovers the normal-subgroup case independently of the open claim
  `fpbs-soft-collapse-on-fg-normal-and-kazhdan-groups`. Remaining survivors:
  torsion Tarski monsters (no infinite proper subgroup), torsion-free Tarski
  monsters (maximal cyclic subgroups expected malnormal, so (C) should fail;
  unchecked) and `B(m,n)` (no subgroup with (C) known). Any remaining test
  case must have every infinite, finitely generated, infinite-index subgroup of
  finite "height" in the sense that some finite intersection of its conjugates
  is finite. This is where soft arguments might still live.

- **Finite-component forests force treeability (2026-09-19,
  swarm-0917-w18-w18-bs-break, operator-algebras).** Established node
  `fpbs-price-one-forests-have-infinitely-many-components`, with route
  `fpbs-price-one-forests-have-infinitely-many-components-proof`.

  If an invariant random spanning forest on a Cayley graph of `Γ` has exactly
  `k<∞` components, then its coset lift with hairs to the marked tree is a
  treeing of a free p.m.p. action of cost `1+(E deg/2-1)/k`. So `Γ` is
  treeable and `C_*(Γ)` equals that value. For nonamenable `Γ` with `C_*=1`,
  Gaboriau's Corollary 2.26 then gives a contradiction. Hence on every Cayley
  graph of every group in this kernel, the FMSF, WMSF, FUSF, WUSF and every
  other invariant spanning forest have infinitely many components almost
  surely.

  **Invariant:** `C_*(Γ)=1`, that is, non-treeability. **Step where every
  member dies:** the hair treeing of the coset lift.

  This is a class-killing obstruction for routes that try to reach `p_c<p_u`
  through a connected, or finite-component, invariant or FIID forest. Examples
  are a connected FMSF, one tree per finite-index coset, and a connected
  spanning forest inside `H_{R,M}`. Every such route is vacuous on the whole
  kernel, so an FMSF-excess proof (`fpbs-msf-excess-equals-nonuniqueness`) must
  control `δ_G` with infinitely many trees. The kernel stays **OPEN**.
* **Derive spines from invariant Cayley cost one through forests
  (host-geometry, 2026-09-19, swarm-0917 w19).** Established
  `fpbs-sparse-spines-iff-sparse-one-ended-forest-connectors`:
  - Sparse spines give sparse inter-tree connectors for *every* one-ended
    invariant forest.
  - Conversely, one-ended forests whose `|desc(o)|` laws are uniformly tight,
    together with `beta`-sparse connectors for every `beta`, give spines.

  Every such pair `F ∪ E'` is a connected spanning graph of cost
  `<= 1 + |S| beta/2`. So spines are exactly invariant Cayley cost one at `S`
  *plus uniform tightness of the descendant tails*.

  The attempted route was to take cheap `H_eps` (expected degree `2+2eps`),
  a spanning forest `F_eps` of `H_eps` of expected degree 2 (for example the
  wired forest), and `E' = H_eps \ F_eps`, which has endpoint density
  `<= 2eps`. **Where it dies:** at uniformity in `eps`. Nothing controls
  `P(|desc_(F_eps)(o)| > n)` as `eps -> 0`. `F_eps` may also have two-ended
  components, whose trunks carry no density bound.

  Intrinsic pruning cannot give tightness. In the unimodular (non-Cayley)
  subdivided 3-regular tree, cost tends to 1, but every invariant connected
  infinite subgraph has density 1. This follows from the MTP: such a subgraph
  must contain the whole of every subdivision path it enters. So spines cannot
  be extracted from `H_eps` alone, and a proof must use `G`-edges outside
  `H_eps` as shortcuts. `fpbs-quantitative-routing-tail-bound` records the
  same pressure as long `H`-routes.

  **Invariant:** tightness of descendant tails of one-ended forests inside
  cost-`(1+eps)` graphs. **Step:** `eps -> 0` with fixed tails.

  A counterexample to spines on a survivor with `c_inv(S)=1` must have
  descendant tails that escape as the price tends to one. The kernel stays
  OPEN.
