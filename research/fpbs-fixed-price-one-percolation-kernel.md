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
