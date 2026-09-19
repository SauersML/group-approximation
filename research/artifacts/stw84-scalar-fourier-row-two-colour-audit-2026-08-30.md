# Audit: two-colour factorization of scalar weighted Fourier rows

Date: 2026-08-30

## Exact factorization

The symbol map is u.c.p. because each point evaluation is a vector-state
compression.  Functional calculus for `U` gives a unital star-homomorphism
from `C(T)`, and cutting it by `h` is c.p.c.  Expanding the composition
recovers every entry of the weighted row exactly.

## Two-colour repair

The circle has nuclear dimension one.  Postcomposition of each of its two
order-zero return colours with functional calculus remains order zero.
Small commutator with `U` gives uniform small commutators with the compact
finite-dimensional return ranges, by common trigonometric-polynomial
approximation.  The cutdown orthogonality defect is therefore small, and
projectivity of finite-dimensional cones repairs each colour inside the
ambient algebra.  The incoming composition remains c.p.c.; no total
contractivity of the two-colour return is assumed or needed.

## Relation to the firewalls

On the diagonal, exact factorization through the averaging state has
maximal overlap depth: all `n` atoms map to the same ray.  This verifies
that the bounded-overlap obstruction has the correct boundary rather than
being an artifact of its proof.  For the full scalar row, non-coordinate
mixing through `C(T)` gives the desired fixed two colours.

The result does not solve the augmentation ideal.  Coefficient-valued
Fourier matrices would require a multiplicative return from
`C(T) tensor D` which simultaneously represents `D` and sends the circle
generator to `U`; that exists precisely in the commuting, not covariant,
situation.  Handling this coefficient/action interaction remains the live
hinge.
