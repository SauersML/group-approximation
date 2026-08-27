---
rg: 2
id: sl3-coherent-building-rounding-gives-action-soficity
kind: route
title: Read coherent framed building quotients as GKEP orbit charts
target: sl3-dyadic-building-vertex-action-is-sofic
requires:
  - sl3-building-deck-cocycles-round-coherently
artifacts:
  - research/artifacts/sl3-building-quotient-label-audit-2026-08-21.md
---

Given finite `F subset A`, `E subset A/C`, and `epsilon>0`, enlarge the
word window so it contains `F`, the products tested for approximate
multiplication, representatives of `E`, and the covariance products
`a x`.  Apply coherent deck-cocycle rounding with a smaller error.

The permutations are an approximately multiplicative map from the tested
part of `A` to a finite symmetric group.  At every good framed vertex the
copy of `E` is injective, and frame covariance is exactly the orbit-chart
intertwining identity.  A union bound over the fixed test window leaves at
least a `(1-epsilon)` fraction of good basepoints.  These are the GKEP
axioms for soficity of `A action A/C`.
