---
rg: 2
title: STW XCV entangled compact corridor audit (2026-08-30)
kind: artifact
---

# Outcome

The compact-bearing representation corridor is narrower than previously
recorded in two independent ways.  Purity makes every representation image
compact-free, with neither faithfulness nor irreducibility required.  It
follows that every genuinely spatial representation of a minimal tensor
product of pure factors is compact-free, even when the factor
representations are reducible.

Second, Takesaki's simplicity theorem, type-I reflection, and an elementary
ideal argument show that a compact-bearing irreducible representation cannot
occur when both pure factors are simple.  Thus any counterexample based on
this engine must use a nonsimple pure factor as well as a genuinely entangled
representation; no unitality assumption is needed.

# Abstract Cu tensor versus the concrete tensor product

For pure `A` and `B`, the abstract Cu tensor product
`Cu(A) tensor_Cu Cu(B)` is pure by `Cu(Z)`-absorption.  This does not make the
concrete semigroup `Cu(A tensor_min B)` pure.  The canonical Cu-morphism need
not be an isomorphism, an order embedding, or surjective; only the
independently proved splitting criterion
`split-cu-tensor-map-implies-pure-product` transfers both regularity axioms
automatically.  An abstract Cu obstruction is therefore not a C-star
counterexample until it is realized in the concrete minimal tensor product.

# Minimal-tensor continuity boundary

A spatial pair of representations on `H_A` and `H_B` always gives a
min-continuous representation on `H_A tensor H_B`.  Normal slice maps are
then available and send compact operators to compact operators.  This is the
mechanism behind the strengthened spatial no-go.

An arbitrary representation of `A tensor_min B`, however, gives commuting
factor actions on one Hilbert space.  Although their multiplication map is
min-continuous by hypothesis, it need not be spatially unitarily equivalent
to a tensor product of factor representations.  There is then no legitimate
slice map from the joint image back into either factor image.  Applying the
spatial slice argument in this setting would be an error.

Conversely, an arbitrary commuting pair initially defines a representation
of the maximal tensor product.  Descent to the minimal tensor product is an
additional norm-continuity requirement.  The property-T diagonal left-right
construction fails exactly here: its compact Kazhdan projection lives in a
maximal-tensor representation that is not min-continuous.

# New exact fences

1. `pure-representation-images-are-compact-free` pulls any nonzero compact
   intersection back to an elementary ideal-subquotient, contradicting
   purity.
2. The strengthened `spatial-pure-factor-reps-have-no-joint-compacts` uses
   slices and (1), and now covers arbitrary factor representations.
3. `stw95-simple-pure-factors-exclude-compact-corridor` combines
   Takesaki's theorem with `type-i-minimal-tensor-reflects-to-factors`.  A
   compact-bearing simple image would be elementary, forcing both simple
   factors to be type I and hence elementary, contrary to purity.

These fences do not settle pure tensor permanence.  They show that the live
compact corridor requires a genuinely entangled min-continuous
representation and nonsimplicity of at least one factor.

# Trust boundary

The only imported theorem in the new packet is Takesaki's simplicity of the
minimal tensor product of simple C-star algebras.  Type-I reflection,
compact-intersection, slice, and ideal-subquotient arguments are proved
directly in the attached routes.  No statement about the abstract Cu tensor
product is treated as a realizability theorem for `Cu(A tensor_min B)`.
