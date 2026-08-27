---
rg: 2
id: tensor-escape-classification-proof
kind: route
title: Combine dense stopping support, tensor scalarization, and bounded-type rounding
target: distributed-tensor-escapes-reduce-to-high-type-coherence
requires:
  - unique-neighbor-ldpc-checks-force-dense-noncommutation
  - bounded-participation-tensor-networks-are-not-diffuse-far
  - tensor-products-cannot-cancel-noncentral-hs-defect
  - bounded-type-noncentral-code-sectors-round-uniformly
---

Apply the stopping-set theorem inside every factorwise-exact representation
to obtain `(DTE1)`.  The bounded-participation theorem removes distributed
bounded-bond networks.  Without a participation bound, apply `(TSC2)` to
every global parity and commutator residual: their total distance from
factorwise scalar words is bounded by twice the global squared defect, so
only scalar phases can cancel at leading order.  Finally use bounded-type
rounding on every tight central type sector.  Any trace that remains far
must therefore escape every fixed type cutoff and carry the unresolved
approximate scalar-phase coherence problem.
