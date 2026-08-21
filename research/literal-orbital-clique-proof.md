---
rg: 2
id: literal-orbital-clique-proof
kind: route
title: Use block equivariance and affine-coset transitivity
target: literal-orbital-graph-block-clique
requires: []
---

An orbital edge is a translate of the marked pair.  The two marked sites
have the same block label and `blockOf` is equivariant, so every edge remains
inside one block.  Conversely, fix two distinct sites with the same block.
After transporting the first to the marked base site, affine-coset
transitivity of its stabilizer moves the second to the marked partner.
Undoing the transport expresses the pair as a translate of the marked edge,
hence it is adjacent.

For the affine carrier, the transitivity hypothesis reduces modulo two to
the three rotation matrices acting transitively on the seven nonzero vectors
of `(F_2)^3`; this finite calculation is the formalized theorem
`conjD_cosetTransitive`.  The other carrier is discharged by the abstract
`alphaCosetTransitive` lemma.
