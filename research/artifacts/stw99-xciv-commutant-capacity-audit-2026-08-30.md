# STW Problem XCIV: finite-dimensional failure and commutant-capacity audit

## The finite-dimensional radius cannot vanish everywhere

If every finite tuple of `R` had operator-norm distance zero from unital
finite-dimensional subalgebras, injectivity of each finite-dimensional
operator system would give a ucp retraction `R->E`.  Inclusion back into `R`
would approximate the identity pointwise in norm, proving CPAP and hence
nuclearity of `R` as a C*-algebra.

This is impossible.  Orthogonal corners in `R` contain a unital block product
`product_n M_n`, which is nonexact for unbounded matrix sizes.  Since
exactness passes to subalgebras, `R` is nonexact and nonnuclear.  Therefore
some finite tuple has strictly positive finite-dimensional norm radius.

This does not produce an XCIV gap: finite-dimensional radius is only an
upper bound for the fixed-block defect.

## Enlarge the approximating cores

A D-capacious core is any unital subalgebra whose relative commutant contains
`D=I_(2,3)`.  If a finite tuple is within `eta` of such a core, the commuting
copy of `D` has commutator defect at most `2 eta`.  The resulting radius
`beta_D` is bounded above by the finite-dimensional radius but also permits
large nonnuclear cores.

Every tensor leg in a decomposition `R=R_0 tensor_bar R_1` is D-capacious,
because the other II1 leg contains `D`.  Hence arbitrary noncommuting finite
tuples in one leg, and tuples norm-close to a leg, have small fixed-block
defect without being approximated by matrices.

## Residual obstruction

A negative fixed-block certificate of size `delta` must remain at distance
at least `delta/2` from every D-capacious core.  This simultaneously excludes
nearby finite-dimensional algebras, diffuse tensor legs, and all other cores
with a commuting dimension-drop block.  Proving that every finite tuple has
zero `beta_D` would solve XCIV, but hyperfinite `2`-norm tensor tails do not
control this operator-norm radius.
