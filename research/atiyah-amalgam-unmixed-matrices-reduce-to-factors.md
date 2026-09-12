---
rg: 2
id: atiyah-amalgam-unmixed-matrices-reduce-to-factors
kind: claim
title: Over an amalgam, a matrix supported in one vertex or the edge has the von Neumann rank it has over that subgroup
distinct_from:
  fournier-facio-one-compressor-subgroup-reduces-to-gamma: that reduces hyperlinearity and soficity of the one-compressor subgroup to the base group Gamma; this reduces the von Neumann kernel dimension of a subgroup-supported matrix over any amalgam to its dimension over the supporting subgroup, an L^2-arithmetic statement.
  algebraic-strong-atiyah-counterexample-exists: that asks for one torsion-free group and matrix with non-integer kernel dimension; this proves where such a matrix cannot be supported, so it locates any amalgam counterexample in the genuinely mixed matrices.
---

**ESTABLISHED.** Let `G = A *_C B`, and let `H` be `A`, `B` or `C`. For every
`M in M_(m,n)(K[H]) subset M_(m,n)(K[G])`,

```text
dim_(N(G)) ker(r_M on l^2(G)^m) = dim_(N(H)) ker(r_M on l^2(H)^m).
```

In particular the value is an integer whenever the Strong Atiyah conjecture
holds for `H`.

**Consequence.** If Strong Atiyah holds for both vertex groups and the edge
group, then every von Neumann kernel dimension over `G` of a matrix supported
in a single vertex or in the edge is an integer. So a Strong Atiyah
counterexample over an amalgam `A *_C B` cannot be supported in one vertex or
in the edge: its support must meet both `A \ C` and `B \ C`. This is the
matrix-level analogue, for amalgams, of
`fournier-facio-one-compressor-subgroup-reduces-to-gamma`, and it applies to the
kernel amalgams `P^(u_1) *_P P^(u_2)` recorded in that node.

Proof: `atiyah-amalgam-unmixed-matrices-proof`.
