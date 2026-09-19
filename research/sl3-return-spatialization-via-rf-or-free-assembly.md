---
rg: 2
id: sl3-return-spatialization-via-rf-or-free-assembly
kind: route
title: Dead — assemble cyclic return models by residual orbit blocks or a free decomposition
target: sl3-noncompact-return-cocycle-spatializes
requires: []
---

**Dead.**  The proposed construction starts with the separately embeddable
cyclic return crossed products and attempts one of two formal assemblies:

1. choose a residual chain `H_j normal Lambda'`, put the translates of one
   canonical profinite-base embedding on blocks indexed by `Lambda'/H_j`,
   and let the finite quotient permute those blocks; or
2. decompose `Lambda'` as a free product, amalgam, or HNN extension of
   subgroups on which the return action is already spatialized, then use the
   corresponding universal property.

The first construction requires the block label to be independent of its
coset representative.  Even allowing inner coordinate changes and finite
matrix amplification, this makes every kernel return `alpha_h`, `h in H_j`,
inner in the translation factor.  The second construction requires a
nontrivial Bass--Serre action of the cocompact lattice.

`sl3-lattice-returns-have-no-canonical-rf-or-free-assembly` rules out both:
the right-lattice map is injective in the outer automorphism group, and the
higher-rank lattice has property FA.  Residual quotient permutations and
separate cyclic embeddings therefore do not produce `(HCS3)`.  The live
claim still permits a noncanonical embedding into `R^omega` on which the
outer kernel returns become spatial; this dead route does not address that
possibility.
