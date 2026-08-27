---
rg: 2
id: finite-projective-v4-holonomy-is-forbidden-sector-blind
kind: claim
title: Scalar projective V4 holonomy cannot detect the forbidden radical sector
distinct_from:
  full-v4-radical-crossed-product-has-one-common-latent-coordinate: that proves the untwisted full translation group synchronizes the three chart labels; this classifies every scalar cocycle modification of the same local cell.
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that rules out all one-dimensional finite restriction graphs; this rules out the most immediate two-cell repair, namely a scalar commutator phase between the two radical transports.
  same-context-s3-endpoint-atlas: that remains open for genuinely matrix-valued holonomy or an unbounded compressor.
---

Keep the action of `V_4=<s_1,s_2>` on `K_f` from `(VRC1)`, but allow the two
transport lifts to have either scalar projective commutator in the marked
sector.  Equivalently, replace the ordinary crossed product by the twisted
crossed product for an arbitrary

```text
omega in Z^2(V_4,T).                                    (PVH1)
```

On every forbidden selector sector the algebra is still

```text
M_(2D_0)(C),                                             (PVH2)
```

independently of `[omega]`.  The reason is that `V_4` acts freely and
transitively on the four radical blocks.  The associated transformation
groupoid is the four-point pair groupoid; every scalar twist on a pair
groupoid is cohomologically trivial.  Its algebra is `M_4(C)`, tensored with
the half-spin algebra `M_(D_0/2)(C)`.

On a satisfying sector, by contrast, `V_4` fixes the unique packet block.
After removing inner implementers, the residual algebra is a twisted group
algebra of `V_4`.  Since

```text
H^2(V_4,T) isomorphic to C_2,                            (PVH3)
```

there are only two possibilities:

```text
C^omega[V_4] isomorphic to C^4          or          M_2(C).  (PVH4)
```

Thus a scalar two-cell can only toggle the satisfying packet between four
`D_0`-dimensional simples and one `2D_0`-dimensional simple.  It is entirely
blind on the forbidden free orbit, precisely where the nonlinear endpoint
law is needed.

In particular, imposing `[s_1,s_2]=1` versus a marked central sign, or using
two copies with opposite scalar commutator phases, does not create forbidden
mass payment.  A finite collection of such cells merely imposes a bounded
list of packet divisibilities, absorbable by taking common direct-sum
multiples.  This is also consistent with the regular stationary flow of
`finite-packet-graph-atlases-have-a-regular-stationary-flow`.

The remaining two-cell must therefore do more than record a scalar Schur
multiplier.  It must act non-scalar on the edge-intertwiner multiplicity
algebra, couple those matrix coordinates to the BCS endpoint convention, or
be iterated by a genuinely unbounded self-similar/compressor relation.

Nor can one exploit the fact that a cocycle choice may leave a single full
matrix block over each selector assignment and search inside it for a literal
word with nonlinear scalar phase.  By
`sectorwise-scalar-finite-group-words-are-selector-affine`, any finite-group
word whose scalar is determined by the marked selector character in every
irreducible already belongs to the elementary-abelian selector subgroup.
