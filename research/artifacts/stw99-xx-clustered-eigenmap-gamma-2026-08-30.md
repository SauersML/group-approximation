---
title: STW XX checkpoint --- Fourier mixing of clustered eigenmaps (2026-08-30)
---

## Positive-coordinate-weight theorem

Uniform Gamma holds for a diagonal AH system whenever, for each fixed early
stage and finite test set, almost all eigenmaps of a sufficiently late
composite can be partitioned into `k`-tuples whose evaluations are uniformly
close on that test set.  There is no restriction on the proportion of
nonconstant coordinate maps.  In particular, the coordinate weight can be
positive or equal to one.

The construction is genuinely non-Cartan.  On each `k`-tuple, use the `k`
rank-one Fourier projections in the multiplicity algebra.  Their flat
diagonals split the normalized trace of every block diagonal matrix exactly,
even when the blocks are unequal.  Uniform closeness of the blocks makes the
commutators small in operator norm.  The unpacketable remainder contributes
at most its normalized cardinality to the mixed-trace error.

An immediate concrete criterion is sublinear eigenmap diversity.  If the
number of distinct eigenmaps in a composite is `o(L)` relative to its total
multiplicity `L`, equal copies can be grouped into `k`-tuples and only
`o(L)` blocks remain.  This gives uniform Gamma even if all the mass comes
from repeated nonconstant coordinate maps.

Exact repetition is not necessary.  The intrinsic refinement
`sublinear-eigenmap-metric-entropy-implies-uniform-gamma` equips the later
eigenmap multiset with the uniform pseudometric induced by an early finite
test set.  A cover by `o(L)` balls at radii tending to zero produces the
required packets, losing at most `k-1` maps per ball.  This permits all `L`
eigenmaps to be distinct and is therefore strictly broader than distinct-map
counting.

## What this says about the Villadsen obstruction

Positive coordinate weight alone cannot obstruct uniform Gamma.  The real
issue in the unresolved first-type examples is the combination of positive
weight with independently variable, low-multiplicity coordinate eigenmaps.
For two genuinely independent coordinate projections and a scalar test
function separating two points of the base, their evaluations are not
uniformly close: the supremum over the product base realizes the full
oscillation of the function.  Therefore the packet theorem does not apply to
the classical multiplicity-one coordinate family.

The same calculation fences a tempting overreach.  A fixed Fourier rotation
between two independent coordinate blocks has commutator norm `1/2` against
`diag(0,1)` at a suitable fibre.  Hence fixed off-diagonal mixing does not
solve the classical Villadsen case.  A witness there would have to vary over
the coincidence stratification in a 2-norm-continuous way.  The theorem does
not provide such a selection and makes no claim that the canonical Cartan
contains a witness.

## Trust boundary

The proof is a finite-stage matrix calculation.  It uses no classification,
Euler-class assertion, or claim about the full central sequence algebra.
The only structural input is the standard diagonal form of the connecting
maps and the fact that traces on a homogeneous building block integrate its
normalized fibre traces.  Elliott--Niu's obstruction concerns witnesses in
the canonical Cartan; the Fourier projections here have off-diagonal packet
entries, so there is no conflict.
