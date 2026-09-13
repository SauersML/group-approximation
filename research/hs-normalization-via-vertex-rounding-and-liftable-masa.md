---
rg: 2
id: hs-normalization-via-vertex-rounding-and-liftable-masa
kind: route
title: Vertex rounding and a liftable masa of the actor commutant, for every model, give Hilbert--Schmidt centralizer normalization
target: kt-centralizer-normalization-hs
requires: [hs-vertex-rounding-and-liftable-masa-force-normalization, hs-stable-vertex-rounding-for-every-model, actor-commutant-has-liftable-masa-in-every-model]
artifacts:
  - research/artifacts/unified-compression-rigidity-2026-09-12.md
---

`hs-vertex-rounding-and-liftable-masa-force-normalization` proves that one trace-preserving
`sigma` satisfying (H1) and (LM) normalizes `sigma(Gamma)' cap prod_U M_n`.
- `hs-stable-vertex-rounding-for-every-model` supplies (H1) for every model.
- `actor-commutant-has-liftable-masa-in-every-model` supplies (LM) for every model satisfying (H1).

With both, every trace-preserving `sigma` normalizes, which is `kt-centralizer-normalization-hs`.
Both inputs are open, so this route does not fire. It supersedes the actor input of
`hs-normalization-via-vertex-rounding-and-actor-gap`: (H2') implies (LM) by
`liftable-masa-from-coarse-actor-gap`, and (LM) is all that is consumed.
