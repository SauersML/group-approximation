---
rg: 2
id: agent-free-compressor-reynolds-affine-ghost-proof
kind: route
title: Dualize the local kernel and exhibit a missing point in a three-point affine span
target: agent-free-compressor-reynolds-zero-has-affine-ghosts
requires:
  - locally-affine-support-bcs-is-exactly-the-lcs-boundary
---

The restriction of `theta` to the finite abelian group `H` is the direct sum
of the characters in `S`, with positive multiplicities.  An element of `H`
lies in the representation kernel exactly when every supported character is
one on it.  Taking annihilators proves `(RAG1)` by finite Pontryagin duality.

In the displayed example, use the commutative representation which is the
direct sum of the three characters in `S`.  Its `110` spectral projection is
literally zero.  Every element killed by all three supported characters is
also killed by their affine product `110`, so `110` is trivial on the local
kernel.  This proves the claimed exact separation between Reynolds vanishing
and kernel separation.

Applying the same calculation context by context gives the locally affine
support criterion.  The cited equivalence identifies that criterion with the
LCS endpoint, so no property of the Reynolds formula alone can supply the
missing global non-CE model.
