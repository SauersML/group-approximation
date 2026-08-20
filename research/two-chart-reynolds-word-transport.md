---
rg: 2
id: two-chart-reynolds-word-transport
kind: claim
title: The two-chart Jacobi cell returns predicate Reynolds averages by finitely many words
distinct_from:
  two-chart-jacobi-action-holonomy: that includes the analytic energy payment and complete compressor interface; this is now the remaining algebraic word-transport component.
---

Construct a finite presentation around the exact `P_n,Q_n` chart cell such
that, after uniform relative exactification of the common `(n-1)`-qubit core:

1. the controlled transverse cell realizes the predicate inclusion
   `A_f<=B_f` on each selector sector;
2. the Fourier chart switch and compressor return uniform enumerations of the
   two finite adjoint Reynolds averages to the same level;
3. the mean squared word-transport error is bounded by a fixed sparse sum of
   defining-relator energies, with overlap bounded independently of `n`; and
4. the parameter drift `r|->ur` and the conjugate local sign `J_n` are both
   expressed by fixed word templates of polynomial derivation cost.

Then `forbidden-packet-reynolds-holonomy-payment` charges every positive
forbidden mass by ordinary normalized-HS energy.

## Attempts

- The exact common core and two one-qubit boundaries are known from
  `truncated-weyl-two-chart-boundary`, so only a fixed finite collection of
  packet words needs pairing. The unresolved algebra is the compressor
  realization of `r|->ur`: multiplication by `u` is additive on each root
  subgroup but is not a unital ring endomorphism of the full elementary
  group. A viable presentation must alternate upper and lower root charts (or
  an Iwahori pair) rather than assert one impossible global endomorphism.

