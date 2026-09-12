---
rg: 2
id: coordinate-block-factorization-under-single-sandwich
kind: claim
title: Single-sandwich division bounds general linear width by 2n+2 over one fixed coordinate block
distinct_from:
  universal-sandwich-ring-is-finitely-presented-and-injective: That adjoins ONE sandwich relation to make ONE chosen element full, and its content is that the coefficient ring stays embedded and finitely presented; this assumes the sandwich for EVERY nonzero element and concludes a matrix-factorization width, saying nothing about presentations or embeddings.
  one-sided-sandwich-leaves-an-ideal-missing-the-core: That is the negative half of the same relation -- one sandwich does not buy simplicity, witnessed by a proper ideal of the Toeplitz algebra; this is a positive elimination statement over rings where the sandwich already holds everywhere, and it is indifferent to the ideal lattice.
  leavitt-gl-equals-el-and-perfect-unit-group: That is an equality of two subgroups over one specific ring, with no width in it and with the binary Leavitt self-similarity doing the transport; this is a bounded-width statement over an arbitrary single-sandwich ring, and it does NOT say the coordinate block is elementary.
  property-tt-mod-t-rigidity-for-elementary-groups: That is the analytic rigidity theorem, whose hypotheses include a Leavitt family, characteristic two and finite type; this is pure matrix algebra over any nontrivial ring with the division property, and it is one of that theorem's inputs rather than a weakening of it.
artifacts:
  - GroupApproximation/PropertyTT/PaperStatements.lean
  - GroupApproximation/PropertyTT/MatrixElimination.lean
  - GroupApproximation/PropertyTT/CoordinateBlocks.lean
  - GroupApproximation/PropertyTT/BoundedGeneration.lean
---

ESTABLISHED, machine-checked, and stated for an arbitrary coefficient ring.
Call `R` *single-sandwich* when

    a != 0  ==>  x a y = 1  for some x, y in R .

`PropertyTTPaper.coordinateBlock_factorization`: for nontrivial single-sandwich
`R`, every `n >= 2` and every coordinate `j` fixed **in advance**, every element
of `GL_n(R)` is a product of at most `2n+2` factors, each either an elementary
transvection or an element of the one coordinate copy

    GL_(n-1)^(j)(R) = { B : B e_j = e_j and e_j^t B = e_j^t } .

The supporting pivot is `PropertyTTPaper.threeMove_diagonalPivot`: one
elementary left factor and two elementary right factors put a literal `1` at a
chosen diagonal coordinate, for any invertible matrix over any single-sandwich
ring.  Exactly one factor of the word is a block element, and the remaining
word has length at most `2n+1`.

## What it is not

It is **not** bounded elementary generation, and the Lean docstring says so:
one coordinate copy of `GL_(n-1)(R)` is part of the generating set, and nothing
here makes that copy elementary.  Turning the width into a statement about
`EL_n` requires a separate diagonal-class hypothesis -- which is why
[[leavitt-gl-equals-el-and-perfect-unit-group]] is a different fact with a
different proof.

It is also not the weaker "some coordinate depending on the matrix" form.
Fixing `j` before `A` is what lets a downstream argument carry **one** relative
subgroup through the whole factorization; the matrix-dependent form would need
a finite permutation argument afterwards and is a strictly weaker width
statement.

## Why the hypothesis is the right one, and where the width is spent

Single-sandwich division is exactly the elimination resource available when
stable-range arguments are not.  A purely infinite simple ring has infinite
Bass stable rank (Ara--Goodearl--Pardo, *K_0 of purely infinite simple regular
rings*, K-Theory 26 (2002), Theorem 2.8(2)), so no stable-range cancellation is
available to shorten a word; and for a nondivision simple ring the same paper's
Theorem 1.6 makes the sandwich property equivalent to pure infiniteness.  So
the class this covers is every unital purely infinite simple ring, and the
`2n+2` is spent as `1 + (n-1) + 1 + (n-1) + 2`: the pivot's one left factor,
the left clearing sweep, the block, the right clearing sweep, the pivot's two
right factors.

## Reusable beyond the lane it was proved for

The statement mentions no field, no characteristic, no Leavitt family and no
representation, so it is available to any lane holding a ring with the division
property -- including the universal sandwich ring of
[[universal-sandwich-ring-is-finitely-presented-and-injective]] once every
nonzero element is full there, which is the shape the ring-quotient route to
the Boone--Higman conjecture is trying to build.  It was proved as the
algebraic input to [[property-tt-mod-t-rigidity-for-elementary-groups]], and
that is the only consumer today.
