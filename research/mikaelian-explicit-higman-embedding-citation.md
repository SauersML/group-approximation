---
rg: 2
id: mikaelian-explicit-higman-embedding-citation
kind: route
title: Import Mikaelian's explicit Higman algorithm
target: mikaelian-explicit-higman-embedding
requires: []
artifacts:
  - research/artifacts/self-similar-dimension-pressure-map-2026-08-20.md
---

**Established by citation.**  V. H. Mikaelian, *An explicit algorithm for the
Higman Embedding Theorem*, arXiv:2507.04347v8 (3 June 2026), Abstract and
Algorithm 1.1, gives the algorithm and the optional two-generator output.
The paper's input terminology is a "recursive group" presented on an
effectively enumerable alphabet by recursively enumerable relations; the
claim records the operational hypothesis to avoid confusing it with a
decidable word problem.

The source builds the output through explicit Higman operations, benign
subgroups, free products with amalgamation, HNN extensions, and the Higman
rope trick.  It does not state the relative Dehn/area estimate needed for
normalized-HS error transport; that separate quantitative role is played by
`quantitative-higman-embedding-with-dehn-control`.

