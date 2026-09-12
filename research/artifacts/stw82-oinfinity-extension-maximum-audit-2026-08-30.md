# STW Problem LXXXII: O-infinity-stable extension audit

## Result

Every extension whose separable middle algebra is `O_infinity`-stable obeys
the nuclear-dimension maximum formula, without assuming nuclearity.

## Dichotomy audit

Toms--Winter, *Strongly self-absorbing C\*-algebras*, Corollaries 3.1 and
3.3 make every nonzero ideal and quotient `O_infinity`-stable.  The required
`K_1`-injectivity holds for `O_infinity`.  Bosa--Gabe--Sims--White,
*The nuclear dimension of O-infinity-stable C\*-algebras*, Theorem A gives
nuclear dimension exactly one for every nonzero separable nuclear
`O_infinity`-stable algebra, including the nonunital and projectionless
cases.  A nonnuclear algebra has infinite nuclear dimension because finite
nuclear dimension implies nuclearity.

Nuclearity is closed under ideals, quotients, and extensions.  Consequently,
if the middle algebra is nonnuclear, at least one endpoint is nonnuclear;
both the middle dimension and endpoint maximum are then infinite.  If the
middle algebra is nuclear, every nonzero term has dimension one.  Zero
endpoints reduce to an isomorphism.  This covers every case.

## Scope

The proof does not require the extension to be full, essential, split,
quasidiagonal, or exact beyond the automatic exact sequence.  It includes
nonnuclear middle algebras, so it is not contained in the previously
recorded dimension-one-middle theorem.  It remains a structural subclass of
Problem LXXXII, not a proof for arbitrary extensions.

The primary inputs are Toms--Winter's absorption permanence for
`K_1`-injective strongly self-absorbing algebras, the Bosa--Gabe--Sims--White
nuclear-dimension-one theorem for nuclear `O_infinity`-stable algebras, and
the Choi--Effros extension permanence of nuclearity.
