---
title: STW XXII stabilized intrinsic L2-selection audit (2026-08-30)
---

## Result

The trace problem has a positive answer for every countably generated
factorial tracial bundle over a compact Hausdorff base of covering
dimension at most one.  The fibres may vary and the bundle need not be
locally trivial or embed into a common finite factor.

This crosses the precise nontrivial-bundle obstruction identified by
Farah--Vaccaro: Michael selection asks for all values to lie in one complete
metric space, while the raw disjoint union of factor fibres has no evident
complete compatible metric.  The intrinsic `L^2` completion is a countably
generated Hilbert `C(K)`-module.  Hilbert-module stabilization embeds all
of its fibres isometrically into one `ell^2`, as the fibres of a
complemented submodule of `C(K,ell^2)`.  This is exactly the missing common
complete metric space.

## Checks which prevent a false disintegration proof

1. An extreme trace supported at `x` initially factors only through the
   norm fibre `M/J_x`, not through the factor fibre `M/K_x`.  The proof does
   not invoke uniqueness of the factor trace until after it has shown that
   `K_x/J_x` is bounded-trace-free.
2. A selected vector in the Hilbert-module completion need not a priori be
   an element of `M`.  The operator-ball identity `(OB)` repairs this.
   Fibrewise spectral clipping is the `L^2` metric projection onto the
   operator unit ball, and tracial completeness makes the clipped
   approximants converge inside `M_1`.
3. Lower semicontinuity is not confused with continuous polar supports.
   High spectral cuts are corrected by polar decomposition; the
   uncontrolled low support is filled arbitrarily into the trace-slack
   complement and is small only after multiplication by `a^(1/2)`.  The
   correction is uniform over all finite factors: after the cut at `eta`,
   the normalized high operators have source defect at most
   `eta^(-1)delta` and mutual inner products at most
   `eta^(-1)delta^(1/2)`.  At the `j`-th polar step the exact recurrence

   ```text
   sigma_j=rho+sum_(i<j)(C E_i+kappa)^2,
   E_j<=sqrt(2sigma_j)+sqrt(sum_(i<j)(C E_i+kappa)^2)
   ```

   forces every high-part error to zero with `delta`.  Trace slack fills
   the missing initial projections, and the low and outside pieces cost at
   most `sqrt(eta)+sqrt(eta+delta)+sqrt(delta)`.  These estimates, rather
   than a qualitative appeal to successive polar decomposition, prove the
   lower semicontinuity used by selection.
4. Approximate `L^2` relations are never fed to a possibly singular gap
   trace.  Michael selection first gives exact source and orthogonality
   relations in every fibre; only those exact identities are used in the
   replication estimate.
5. Uniform local path connectedness does not use hyperfiniteness.  A unitary
   simultaneously maps the finitely many orthogonal polar frames, and its
   principal-logarithm path contracts the weighted `L^2` displacement.

## Scope and remaining boundary

For uniform completions of separable C-star algebras, countable generation
is automatic.  Thus the theorem covers nontrivial factorial Bauer bundles
with compact extreme boundary of dimension at most one.  It does not solve
Problem XXII in higher or infinite covering dimension.  Michael selection
there requires uniform local higher connectivity of the varying-factor
weighted-copy values; pointwise contractibility of each unitary group does
not supply the needed uniform family modulus.

The theorem also does not assert that the norm-fibre gap vanishes.  It may
be nonzero; the conclusion is exactly that it carries no bounded positive
trace.

## Literature boundary

Farah--Vaccaro, *Continuous Selection of Unitaries in II_1 Factors*,
arXiv:2501.01272, proves the one-dimensional trace theorem for **trivial**
W-star bundles with one fixed factor.  Its concluding discussion explicitly
leaves nontrivial bundles open because the disjoint union of their fibres
lacks an evident common complete metric.  The stabilized intrinsic
`L^2`-module is what removes that obstruction here.
