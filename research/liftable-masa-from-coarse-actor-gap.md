---
rg: 2
id: liftable-masa-from-coarse-actor-gap
kind: route
title: A coarse gapped block decomposition of the actor lifts a masa of its relative commutant
target: actor-commutant-has-liftable-masa-in-every-model
requires: [hs-coarse-actor-gap-at-compressor-generators, hs-block-gap-iff-liftable-masa-of-actor-commutant]
artifacts:
  - research/artifacts/hs-coarse-gap-aspect-scales-2026-09-12.md
---

Let `sigma` satisfy (H1) and take blocks `q_A` from
`hs-coarse-actor-gap-at-compressor-generators`, with `tau(1 - p) -> 0`.

1. Adjoin `q_0 = 1 - p` as one more block. Its boundary is at most `2 tau(q_0)^(1/2) -> 0`, so the
   partition of unity `{q_0} cup {q_A}` has vanishing summed boundary.
2. Clause (b) on every block `A`, multiplied by `tau(q_A)` and summed, gives the summed gap (F2)
   with constant `kappa'` for block-diagonal self-adjoint contractions supported on `p`. On `q_0`
   the discrepancy is bounded by `2 tau(q_0)`, which is absorbed into the `epsilon` of (F2).
3. Item 4 of `hs-block-gap-iff-liftable-masa-of-actor-commutant` makes `prod_U C_n` maximal
   abelian in `sigma(G)' cap M`, where `C_n` is the span of the partition.

So (H2') for every model implies (LM) for every model.
