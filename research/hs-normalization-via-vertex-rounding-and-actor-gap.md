---
rg: 2
id: hs-normalization-via-vertex-rounding-and-actor-gap
kind: route
title: Vertex rounding and a center-compatible coarse actor gap give HS normalization through the proved median assembly
target: kt-centralizer-normalization-hs
requires:
  - hs-rounding-and-actor-gap-force-ccr
  - hs-stable-vertex-rounding-for-every-model
  - hs-coarse-actor-gap-at-compressor-generators
artifacts:
  - research/artifacts/hs-s4-assembly-2026-09-12.md
---

`hs-rounding-and-actor-gap-force-ccr` proves that one trace-preserving `sigma` satisfying (H1) and (H2')
normalizes `sigma(Gamma)' cap prod_U M_n`.
- `hs-stable-vertex-rounding-for-every-model` supplies (H1) for every model.
- `hs-coarse-actor-gap-at-compressor-generators` supplies (H2') for every model, at a generating set of
  vertex generators and strict compressors.

With both, every `sigma` normalizes, which is `kt-centralizer-normalization-hs`.

Both inputs are open, so this route does not fire. Its role is to name exactly what remains: the
median assembly (S4-S6) is no longer a gap.
