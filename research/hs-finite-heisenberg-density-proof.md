---
rg: 2
id: hs-finite-heisenberg-density-proof
kind: route
title: Decompose each exact finite Heisenberg representation in the tracial ultraproduct
target: hs-finite-heisenberg-windows-have-compatible-density-measures
requires: []
---

The defining multiplication table of a fixed finite window contains only
finitely many group words.  Vanishing normalized-HS multiplicative defect
makes those words an exact representation of `H(A,B,C)` in the tracial
matrix ultraproduct.  Its finite-dimensional group algebra decomposes as

```text
C[H]=directSum_(pi in Irr(H)) M_(dim pi)(C).
```

The images of the primitive central projections are orthogonal and sum to
one.  Taking the finite trace gives `(HHD1)--(HHD2)`.  Restriction of a
primitive block to a smaller finite window is the usual finite direct sum of
irreducibles, so trace additivity gives exactly the integral branching
identities.

Finite-dimensional C-star algebras are flexibly stable in normalized
Hilbert--Schmidt norm.  Applying the standard averaging/polar correction to
the fixed multiplication table realizes the same weights by coordinate
representations after changing `o(d_n)` dimensions, which proves the
coordinate formulation.

For an involution `v`,

```text
||(1-u(v))/2||_2^2=(1/4)||u(v)-1||_2^2.
```

The left side is the trace of its spectral projection, giving the final
positive-density assertion.

