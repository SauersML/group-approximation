---
title: STW XI audit --- lattice-coupled products of cyclic systems (2026-08-30)
---

## Result

For any integer lattice map `L:Z^d->Z^m`, couple arbitrary homeomorphisms
`alpha_i:X_i->X_i` through the coordinate formula

```text
g.(x_i)_i=(alpha_i^(L(g)_i)(x_i))_i.
```

For this entire class, stable finiteness, quasidiagonality, and
AF-embeddability of the crossed product are equivalent.  They are also
equivalent to Pimsner incompressibility of every cyclic factor on which the
lattice image acts nontrivially.

This is a higher-rank conclusion, not a relabelled cyclic action.  For example,
the matrix

```text
[1 2]
[3 1]
```

couples two arbitrary homeomorphisms into a rank-two `Z^2`-action in which
both standard generators move both spaces.  Stable finiteness alone forces an
AF embedding.  Rank-deficient, diagonal, and skew lattice images are covered
as well.

## Proof audit

There are four points at which an apparently formal tensor-product argument
could fail; each is handled explicitly in the route.

1. The kernel of the lattice map acts trivially.  Its quotient is the free
   abelian group `H=L(Z^d)`, so the extension splits and contributes exactly
   the commutative factor `C*(ker L)`.
2. For an active coordinate, a group element with nonzero coordinate produces
   a faithful copy of a crossed product by a nonzero power of that coordinate
   homeomorphism.  Faithfulness follows from the coefficient expectations; it
   does not require the lattice image to contain a coordinate vector.
3. If one positive power of a homeomorphism has no Pimsner compression, then
   neither does the homeomorphism: a compression is nested and remains a
   compression for every positive power.  Negative powers give isomorphic
   crossed products.  Thus stable finiteness of the coupled algebra activates
   Pimsner's AF embedding separately in every visible coordinate.
4. A subgroup crossed product embeds in the crossed product by the ambient
   free abelian coordinate group because the groups are amenable and the
   reduced coefficient expectations are faithful.  The ambient coordinate
   crossed product is the tensor product of the one-dimensional crossed
   products.  Inactive coefficient factors and the kernel torus are
   commutative and hence AF-embeddable.

The result assumes neither a faithful invariant measure nor tracelessness, so
it does not collapse into either global regime already recorded on Problem XI.
It also assumes no zero-dimensionality or compact-open support filtration and
concludes the stronger AF-embeddability statement unavailable from the earlier
gluing routes.

## Source and scope check

The cyclic input is Mihai Pimsner, *Embedding some transformation group
C*-algebras into AF-algebras*, Ergodic Theory Dynam. Systems 3 (1983),
613--626, DOI 10.1017/S0143385700002182.  The publisher's primary record states
the AF-embedding/pseudo-non-wandering equivalence; STW's theorem immediately
before Problem XI records the equivalent stable-finiteness and open-compression
form used here.

A primary-source search through 30 August 2026 found results for cyclic
systems, faithful invariant measures, and specialised higher-rank actions, but
no statement matching the arbitrary lattice-coupled product theorem above.
This audit records a new repository theorem, not a claim of literature
priority.  It does not settle Problem XI for actions which do not admit the
product-of-cyclic presentation `(LC1)`.
