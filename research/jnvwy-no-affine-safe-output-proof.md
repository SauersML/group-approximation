---
rg: 2
id: jnvwy-no-affine-safe-output-proof
kind: route
title: Reflect affine safety backward through answer reduction and oracularization
target: jnvwy-active-output-has-no-affine-safe-perfect-model
requires:
  - jnvwy-introspection-has-no-affine-safe-perfect-model
  - jnvwy-perfect-answer-reduction-reflects-affine-safety
  - jnvwy-perfect-oracularization-reflects-affine-safety
---

Assume an affine-safe perfect model of the output of one active compression
round.  Apply the exact accepted-proof-atom coarse-graining to recover an
affine-safe perfect typed-oracle model.  Apply the exact oracle-marginal
coarse-graining to recover an affine-safe perfect introspection model.  The
full-seed Weyl argument supplies a positive odd list on the
Intro--Sample edge whose xor is rejected, a contradiction.

Every implication stays inside the original measurement algebra and uses
only coarse-graining, products of commuting marginals, and finite odd sums.
It therefore preserves tensor, commuting, and faithful-tracial model type.
