---
rg: 2
id: mikaelian-explicit-higman-embedding
kind: claim
title: A recursively presented group can be explicitly embedded into an explicit two-generator finitely presented group
artifacts:
  - research/artifacts/self-similar-dimension-pressure-map-2026-08-20.md
distinct_from:
  quantitative-higman-embedding-with-dehn-control: that assumes a time-bounded decidable word problem and controls relative area; this theorem is an explicit algorithm for a recursively enumerable presentation and provides no comparable quantitative area bound.
  torsion-free-higman-embedding: that preserves torsion-freeness; this theorem instead makes the classical Higman construction explicit and optionally reduces the host to two generators.
---

There is an explicit algorithm which takes an effectively enumerable set of
generators and recursively enumerable defining relations for a group `G` and
outputs:

1. a finite presentation of a group `H`;
2. explicit words describing an embedding `G -> H`; and
3. optionally, a finite presentation of a two-generator finitely presented
   overgroup containing `H`.

This is an effectivity theorem, not a quantitative-HS compiler.  In
particular, it does not bound the area in the output presentation of an input
relation as a function of the input computation time.  Therefore it can make
a self-referential recursive construction explicit, but it cannot replace the
runtime-independent semantic transport required by `hs-pcp-boone-compiler`.

