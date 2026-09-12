# STW Problem XCIV: exact-core barrier audit

## Statement audited

Some finite tuple in the hyperfinite factor `R` stays a positive
operator-norm distance from every exact unital C-star subalgebra of `R`.

## Local exact approximation would force exactness

If every finite tuple could be approximated arbitrarily well by an exact
subalgebra, approximate a basis of any finite-dimensional operator subspace.
Finite-dimensional stability of completely bounded norms turns the basis
perturbation into a complete near-isometry into that exact subalgebra.
Kirchberg's local operator-space criterion would then make `R` exact.

The approximation tolerance is allowed to depend on the chosen basis and
dimension.  No dimension-uniform perturbation estimate is asserted or
needed.

## The ambient factor is not exact as a C-star algebra

Choose orthogonal corners in `R` with strong sum one and place `M_n` in the
`n`th corner.  Bounded strong block sums embed `product_n M_n` unitally and
isometrically into `R`.  The unbounded matrix product is nonexact by the
standard Wassermann obstruction, and exactness is hereditary to C-star
subalgebras.  Hence `R` is not exact.

## Consequences and firewall

The negation of local approximation yields one finite tuple with a uniform
positive distance from every exact subalgebra.  Since nuclearity implies
exactness, this rules out all nuclear, AF, ASH, finite-nuclear-dimension, and
exact `Z`-stable cores for that tuple.

This does not produce a positive commutator gap for `I_(2,3)` and does not
refute XCIV.  A `Z`-stable algebra need not be exact.  It instead shows that
any universal positive core construction must reach genuinely nonexact
`Z`-stable subalgebras for at least one finite tuple.
