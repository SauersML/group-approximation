# Audit: alternating-shift coherent-stage stress test

Date: 2026-08-30

## What is proved

For `Alt_fin(Z)`, every finite coefficient packet is contained up to an
arbitrarily small error in a finite group algebra on which the shift is
implemented exactly by a group unitary lying in a larger finite group
algebra.  This proves the strongest natural finite-set-only covariance
condition.

The same group unitary can never be approximately shift fixed: for every
nontrivial finitary permutation `p`, the norm gap between `lambda_p` and
its translate is at least `sqrt(3)`.  The constant follows from the exact
spectrum of a nontrivial finite-order regular unitary.  Thus the obvious
partial-translation stages cannot satisfy coherent innerness.

Whole-stage coherent innerness implies approximate representability because
the estimate can be tested on the implementing unitary itself.  The
coefficient approximation costs only three times the stage tolerance.
Approximate representability is equivalently the Rokhlin property for the
dual circle action; see E. Gardella, *KK-theory of circle actions with the
Rokhlin property*, Proposition 2.8(2), DOI
`10.4153/S0008414X25000112`.

## What is not proved

The `sqrt(3)` obstruction applies to group unitaries, not to arbitrary
unitaries in arbitrary finite-dimensional subalgebras of `C*(Alt_fin(Z))`.
Accordingly the package does **not** claim that the alternating shift fails
approximate representability, nor that it fails coherently inner finite
stages.  It identifies approximate representability as a necessary gate and
rules out the entire natural group-stage realization.

Exact covariance on a proper coefficient subalgebra does not rescue the
Haar proof.  The `M_2 tensor M_2` example has exact commutation on the first
tensor factor while the residual unitary remains distance one from the
commutant of the full stage.  A finite control set works only if it is a norm
net for the eventual stage's whole unit ball, which is merely a finite
reformulation of the original uniform hypothesis.

## Consequence for LXXXIV

The alternating shift is not obstructed at the coefficientwise covariance
level: that level is exact.  The missing datum is a shift-almost-fixed
implementer, followed by uniform control on the finite-dimensional stage
that contains it.  Any proof of the cyclic augmentation core via the
coherent-stage theorem must therefore construct genuinely non-group
unitaries and cross this fixed-implementer gate.
