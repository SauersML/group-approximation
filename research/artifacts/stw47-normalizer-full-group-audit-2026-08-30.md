---
rg: 2
title: STW XLVII normalizer-full-group criterion audit (2026-08-30)
kind: artifact
---

# Scope

This artifact audits an intrinsic recognition theorem for Cantor
C-star-diagonals.  It does not assert that every C-star-diagonal in an AF
algebra passes the criterion, so it does not close the sharp universal form
of STW Problem XLVII used by the root node.

# Exact criterion

For a separable unital C-star-diagonal pair `(A,D)` with Cantor spectrum,

```text
D is an AF Cartan
    <=> N_U(A,D)/U(D) is a locally finite group.
    <=> C*(D,F) is subhomogeneous for every finite F subset N_U(A,D).
```

The quotient is intrinsic to the inclusion.  It is canonically the
topological full group of the principal Weyl equivalence relation.  The
kernel is exactly `U(D)` by maximal abelianness.  Surjectivity is not an
untwisted assumption: every circle bundle over the compact zero-dimensional
graph of a full bisection has a clopen trivialization and hence supplies a
unitary normalizer.

# Two directions checked

If the pair is AF Cartan, finitely many full normalizers lie at one compact
finite-relation stage.  A finite clopen sheet refinement embeds the generated
quotient group into a finite product of symmetric groups.

If the quotient is locally finite, enumerate it by finite generated
subgroups.  Their graphs are compact-open finite equivalence relations.  A
single off-diagonal arrow is captured by the full-group involution obtained
from a small bisection, its inverse, and the identity outside their disjoint
source and range.  Hence these finite relations exhaust the Weyl relation.

For the local C-star formulation, a finite normalizer packet generates a
group `H` of Weyl homeomorphisms.  If `H` is finite, its relation has uniformly
finite orbits, so the intermediate twisted relation algebra is
subhomogeneous.  In the reverse direction, an `N`-subhomogeneous intermediate
algebra forces every irreducible orbit representation `ell^2(Hx)` to have
dimension at most `N`.  A `k`-generated group acting faithfully with all
orbits of size at most `N` is finite: after identifying each orbit with at
most `N` letters, only finitely many `k`-tuples of permutations, hence only
finitely many point-stabilizer kernels, can occur.  Their intersection is
trivial and finite-index.

# Twist audit

AF Cartans have trivial Weyl twist, so merely proving that the underlying
relation is AF would leave a logical gap unless twists over AF relations are
also controlled.  They are.  A multiplicative section on one compact finite
subrelation extends across the next one on saturated clopen reductions pulled
back from the zero-dimensional quotient by the larger finite relation.  On
each reduction choose old-class anchors, take the base connector to be the
canonical unit, and choose the remaining connector lifts.  The formula

```text
(old lift to anchor) (connector) (inverse connector)
    (old lift from anchor)
```

both preserves the old section and is multiplicative by cancellation.
Induction trivializes the twist on the full AF relation.  This argument uses
the Cantor/zero-dimensional hypothesis essentially for coherent clopen
choices.

# Independent provenance check

The groupoid middle equivalence agrees with Hiroki Matui, Proposition 3.2 in
*Some remarks on topological full groups of Cantor minimal systems*
(arXiv:math/0404117): an etale equivalence relation on a Cantor set is AF if
and only if its topological full group is locally finite.  The route includes
the proof rather than treating that citation as a premise.  The additional
normalizer-quotient and coherent-twist steps are written out in the route.

# Remaining hinge for XLVII

For an ambient AF algebra `A`, the unresolved implication is now the concrete
statement

```text
D subset A is a Cantor C-star-diagonal
    => N_U(A,D)/U(D) is locally finite.
```

A counterexample has a finite tuple of normalizing unitaries whose images
generate an infinite group, and the corresponding intermediate algebra over
`D` is not subhomogeneous.  This finite witness is sharper than saying only
that the principal Weyl relation is not AF and gives a direct target for
finite-dimensional perturbation arguments inside the ambient AF algebra.
