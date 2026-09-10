---
rg: 2
id: fpbs-critical-dyadic-projection-estimate
kind: claim
title: Critical dyadic cluster-averaging projections have summable size-weighted operator norms
---

OPEN research hypothesis Q2 for every nonamenable Cayley graph. Q3 is a stronger optional estimate; neither is established.

## Attempts

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
