---
rg: 2
id: linear-reversible-words-strict-via-strict-linear-factor-proof
kind: route
title: Induct from the right on suffix surjectivity
target: linear-reversible-words-strict-via-strict-linear-factor
requires:
  - certificate-linear-automata-have-local-linear-decoders
artifacts:
  - research/artifacts/low-degree-strict-pairs-linear-parts-2026-09-12.md
---

Section 8 of the artifact.

1. Put `S_j = W_j ... W_n` and `S_(n+1) = id`.
2. Suppose `S_(j+1)` is surjective. Injectivity of `tau` makes `S_j` injective, so `W_j` is
   injective on the whole configuration space.
3. A bijective factor keeps `S_j` surjective. An injective square linear factor is surjective or
   strict.
4. `tau = S_1` is not surjective, so some square linear factor is strict. It has a linear left
   inverse (`certificate-linear-automata-have-local-linear-decoders`), so `C A = I != A C`.
