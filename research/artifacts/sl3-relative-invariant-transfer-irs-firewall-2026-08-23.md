# IRS rigidity does not decide the dyadic SL3 action

An exact consequence of the GKEP ultraproduct definition is:

> if the original countable set action is faithful, the Loeb permutation
> action attached to every sofic atlas is essentially free.

Indeed, a root fixed by `g` forces the atlas labels of `x` and `gx` to agree
at that root; their distance-one separation makes this a null event whenever
`gx!=x`.

The action of `SL_3(Z[1/2])` on the type-zero building vertices is faithful.
Its kernel is the normal core of `SL_3(Z)`; the higher-rank normal subgroup
theorem and infinite index make the core central, and the center is trivial.

Therefore a hypothetical sofic model has stabilizer IRS `delta_{e}`.  This
is fully compatible with every higher-rank IRS classification.  At the same
time its Koopman representation contains the quasi-regular vector fixed by
`SL_3(Z)` and moved by the dyadic group.  There is no conflict: the
stabilizer of a vector/function is not the stabilizer of a typical Loeb
point.

This removes IRS and character rigidity as possible dimension-free proofs
of relative invariant transfer.  The surviving target must control the
specific Koopman subrepresentation or the moving atlas labels, not merely
the point-stabilizer distribution.

