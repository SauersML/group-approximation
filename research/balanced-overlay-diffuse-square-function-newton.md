---
rg: 2
id: balanced-overlay-diffuse-square-function-newton
kind: claim
title: Correct the low-square-function balanced overlay by operator-row Newton iteration
distinct_from:
  quadratic-overlay-has-uniform-linearized-synchronization-gap: that supplies an ordinary normalized-HS Jacobian gap at exact points; this must propagate the gap and control nonlinear remainders in the operator row-column square-function norm away from an already known exact base
  balanced-overlay-common-reducing-outlier-cut: that removes the high square-function spectral sector; this corrects the remaining diffuse block
---

OPEN.  On the complement of the common cut from
`balanced-overlay-common-reducing-outlier-cut`, use the operator bound on the
average residual square function to enter and run a dimension-independent
Newton or alternating-projection basin for the balanced occurrence
presentation.

## Attempts

The ordinary Jacobian gap at exact representations does not immediately
give this statement: the low block controls an **average row/column square
function** of residuals, not the operator norm of every residual and not the
operator distance to a previously identified exact representation.  The
promising route is to rewrite the character-block complete-graph inverse and
the equality-expander inverse as completely positive averages.  Such
averages are contractions in operator row/column norm, which would make the
quadratic remainder bounded by `O(sqrt(b))` times the current `2`-residual.
What is still unproved is an SOS/coercivity identity extending the exact
character-block Jacobian inverse to a tuple known only through this
square-function bound; assuming the exact character decomposition here
would be circular.

The positive part is now explicit:
`code-laplacian-has-uniform-cp-green-approximants` supplies dimension-free
finite CP Green polynomials for the exact adjoint code Laplacian and the
equality expanders.  The remaining inverse is the coordinate-gradient
assembly below; an `L_2` Green tail cannot be promoted to cb convergence by
itself.

`complete-overlay-row-newton-is-a-code-riesz-multiplier` sharpens even the
exact-base part: the characterwise inverse formulas assemble into a
vector-valued code Riesz Schur multiplier.  The HS inverse is automatic, but
the needed operator row/column estimate is a cb bound for that multiplier
(or a BMO estimate with summable John--Nirenberg cuts).  After that linear
estimate is obtained, one must still perturb it from exact bases to tuples
controlled only by the diffuse square function.

The nonlinear dense layer itself is no longer an obstruction:
`dense-complete-pair-remainders-are-cb-quadratic` proves the required
dimension-free row/column quadratic estimate by factoring the full double
average through the coordinate square function.  The unresolved interaction
is with the sparse bounded-template layers.  One must alternate exact local
parity-face projection and equality-cloud alignment with the dense step and
show that these local corrections preserve (or contract back into) the
global row basin.  A coordinatewise Taylor bound would reintroduce the
forbidden sparse high-operator-norm loss.

The random-prefix martingale realization has also been audited.
`code-riesz-inverse-is-averaged-first-split` proves the exact formula for
every code-character subset, while
`junge-riesz-bmo-does-not-close-code-newton` records that fixed-permutation
BMO loses `sqrt(L)` and row-valued John--Nirenberg produces a projection in
`M_L tensor M_d` rather than one common physical cut.  The precise
martingale target is therefore a permutation-averaged BMO estimate followed
by an exponential tail bound for the physical coordinate square function
(or a product-cut theorem for the amplified Cuculescu projection).

There is a finite-moment gain short of that endpoint.
`code-gap-gives-finite-p-inverse-square-root` shows that the scalar
inverse-square-root Laplacian factor has amplified `L_p` norm at most
`sqrt(2p/delta)` under relative code distance `delta`.  Thus this factor no
longer obstructs any fixed-`p` truncation scheme.  What remains is to place
the layer-dependent two-form array in the correct tangent row/column module
with a compatible finite-`p` Riesz/divergence estimate, then convert those
moments into one approximately reducing projection in the physical matrix
algebra.  The estimate does not supply either step or an endpoint cb bound.

The genuinely noncentral remainder is now localized further.
`bounded-type-noncentral-code-sectors-round-uniformly` uses compactness of
empirical reflection measures to round every shared-reflection sector whose
generated algebra has uniformly bounded irreducible type, followed by the
ordinary scalar LTC decoder.  Therefore a diffuse far countermodel cannot
be assembled from fixed nonabelian packets or bounded matrix blocks: it must
retain positive trace in irreducible dimensions tending to infinity.  The
present Newton gate must control precisely that unbounded-type mass (and
still cannot assume occurrence synchronization in order to define the
shared generated algebra).

The obvious unbounded-type stress test is also excluded.
`balanced-parity-excludes-perfect-matching-pauli-mixtures` analyzes direct
sums of exponentially large Clifford blocks indexed by perfect matchings.
Although each fixed pair then has only `O(1/L)` global commutator energy,
the Pauli parity syndromes are charged at constant density by the balanced
original layer; if most syndromes are repaired, robust erasure cleaning
rounds the remaining projective block.  Thus the unresolved high-type mass
must be genuinely noncentral, not a diffuse central sum of matching Pauli
packets.
