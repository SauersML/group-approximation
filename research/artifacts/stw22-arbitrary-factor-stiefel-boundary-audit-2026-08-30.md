# STW XXII arbitrary-factor Stiefel boundary audit (2026-08-30)

## Exact reduction

For a projection weight, an orthogonal `m`-tuple is not a new configuration
space: relative to one base frame it is exactly one partial isometry with
initial projection equal to the sum of the base ranges.  The trace
calculation in `(SB1)` is exact, so the Hilbert-sum tuple metric becomes the
ordinary `L^2` metric on a single Stiefel space.  The maximum tuple metric
only introduces the fixed factor `sqrt(m)`.

For a general positive weight, polar decomposition gives the same
homogeneous orbit, with the metric weighted by the transported positive
element.  The established high/low spectral-cut argument reduces its local
loop problem to the projection-weight problem plus a low-weight extension.

## Why strict slack is load-bearing

At zero slack the fibre can be the whole unitary group.  Normalized matrix
traces then make determinant-degree-one winding loops arbitrarily small in `L^2`
as the dimension grows, while the determinant still detects their nonzero
homotopy class.  Thus no factor-independent local loop-filling modulus is
possible without a uniformly nonzero complement.

This obstruction is sharp topologically in matrices.  Once the complement
has positive rank, the complex Stiefel manifold is simply connected.  The
remaining issue is quantitative rather than ordinary homotopy: one needs a
filling that stays in a prescribed `L^2` ball with a modulus independent of
matrix size and of the finite factor.

## Trust boundary

This reduction is not by itself a dimension-two solution. Its two successor
packages now close the projection-weight quantitative problem: the matrix
case by finite-rank defect localization and the diffuse case by a summable
continuous spectral carrier followed by strong-topology contraction. The
remaining arbitrary-positive-weight diffuse step is relative: low spectral
frames must be extended in the moving complement of the high-frame filling.
