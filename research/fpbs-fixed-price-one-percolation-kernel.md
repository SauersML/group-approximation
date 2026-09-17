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
