---
rg: 2
id: hrf-next-affine-radicals-preserve-detector-image-proof
kind: route
title: Separate inflation and alternating forms, then compute agreement of conjugate complement lifts
target: hrf-next-affine-radicals-preserve-detector-image
requires: []
artifacts:
  - research/artifacts/hrf-next-attack-2026-09-20.md
---

The complete elementary proof is Sections 1a--4 of the artifact.
Section 1a defines the discrepancy maps without an external detector
theorem: vanishing vertex `H^2` gives lifts into any central extension,
and perfectness makes them unique. On each edge their central ratio is
a homomorphism. Extension equivalence preserves it, Baer addition adds
it, scalar pushout scales it, and pullback preserves it. These facts
prove well-definedness, linearity, and the naturality used below.

Since the vertices are perfect, the surjective image `Q` is perfect,
so `V_S=0`. In any central `k`-extension of `Q`, the pth-power map on
`V` is an invariant linear form and therefore zero; its commutator map
is an invariant alternating form `b`. The explicit Heisenberg extension
`(V x k,b/2) semidirect S` realizes this form. Subtract it and the
inflation of the restriction to the standard complement `S`.

The remaining extension splits over both `V` and `S`. Comparing these
sections under conjugation gives a cocycle in `Z^1(S;V*)`. The assumed
vanishing lets one change the vector-group section to be equivariant,
giving a global splitting. Thus every class is an inflated class plus
one of the displayed Heisenberg classes.

For each vertex, its affine cocycle is a coboundary, so its map is a
conjugate by some vector `v_i` of its map into the standard complement.
In the Heisenberg extension the unique vertex lift has central
coordinate `-b(v_i,sv_i)/2`. Equality of two vertex images on an edge
gives `s(v_i-v_j)=v_i-v_j`; invariance and alternation of `b` then give
`b(v_i,sv_i)=b(v_j,sv_j)`. Hence every Heisenberg class has zero
discrepancy. Inflated classes have exactly the base discrepancies,
which proves the pointwise identity. Inflation is a right inverse to
restriction to `S`, so the images are equal.

Odd characteristic, surjectivity, dual-module `H^1`, and the vertex
coboundary condition are all used; none is silently discarded.
