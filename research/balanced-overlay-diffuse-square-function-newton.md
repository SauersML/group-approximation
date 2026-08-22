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

However, generated-algebra type itself cannot be used as the next coercive
quantity.  `high-type-mass-is-discontinuous-at-exact-code-tuples` perturbs
one reflection of an exact diagonal all-local-dual code tuple by an
arbitrarily small generic conjugacy.  Every balanced relator then has
vanishing maximum defect and the tuple remains inside the correct basin,
but its generated algebra is the full `M_d`, with `d` arbitrary.  Hence no
fixed standard-polynomial/subhomogeneity estimate can charge high-type mass.
The remaining argument must be metric and generator-local; it cannot first
truncate the entire generated algebra by irreducible dimension.

The strongest cardinality-free PVM orthogonalization theorem also lands
exactly on this boundary.  `de-la-salle-full-pinching-rounds-one-reflection`
rounds a reflection against an already exact joint PVM with constant `20`,
but its input is the whole joint-pinching disturbance.  The exact Fourier
calculation `joint-pinching-costs-linear-generator-gap` shows that averaged
commutators with `k` commuting generators control that disturbance only with
a sharp factor `k`, attained by a weight-one adjoint character.  Therefore
iterating two-PVM orthogonalization cannot replace the missing parity-aware
row/column coercivity.  A successful Newton argument must use the balanced
parity layer to exclude or correct those low-weight adjoint modes before it
invokes the orthogonalization theorem.

There is now a complete **transverse** theorem once a commuting reference
enters the basin.  `code-distance-upgrades-pair-energy-to-full-pinching` first
decodes any commuting reference atomwise to the code, then uses relative
code distance to force every nonzero adjoint Fourier character to have
weight `Omega(L)`.  De la Salle consequently rounds any further reflection
against that code PVM with a length-independent constant.  Thus the
low-weight Fourier obstruction belongs entirely to **basin capture**: the
all-local-dual tail inequalities may peel its sparse coordinate support,
but the still-missing diffuse estimate must construct one commuting
reference on the shortened core.

This does not yet give simultaneous terminal rounding.  The zero adjoint
character is the full within-code-atom multiplicity algebra, and de la
Salle's correction leaves that algebra untouched.  For example, when the
reference has one atom (`S_i=I`), an arbitrary reflection already commutes
with it at zero cost.  The remaining noncentral diffuse gate can therefore
be stated precisely: balanced local parity plus complete-pair energy must
centralize these multiplicity blocks, or refine them to one common abelian
code PVM, without losing the transverse constant proved above.

Random coordinate anchoring gives a complementary exact-base realization
of the desired gap.  `random-code-anchor-pinchings-contract-exact-transverse-energy`
shows that one uniformly random coordinate pinching contracts every
off-diagonal code-character block by `1-delta`, and that pinching followed
by reflection sign-rounding costs at most one half of the selected anchor's
commutator energy.  Iterated anchors preserve all earlier commutants.  The
remaining obstruction is exactly basin entry, not the anchor calculation:
`random-anchor-contraction-does-not-yet-enter-the-diffuse-basin` records
that the code-character blocks used in the proof do not exist before
synchronization, while local parity re-exactification either splits shared
coordinates or becomes the original global rounding problem.  A successful
version must prove expected contraction of the **full** balanced energy
directly from the diffuse square function, with an equality-compatible
global correction; ordinary triangle bounds supply boundedness but no
strict contraction.

The one-anchor nonlinear algebra is now sharper than that coarse triangle
audit.  `one-anchor-grading-makes-parity-damage-quadratic` decomposes every
reflection into even and odd parts for the selected anchor.  Pinching a
parity word kills all odd-cardinality terms, so its difference from the
product of the pinched factors begins with **two** odd factors; the pair
commutator has the exact analogous formula, and spectral sign-rounding is
quadratic whenever the odd part is operator-small.  Thus random anchoring
really has the Newton form “CP-contracted linear residual plus quadratic
remainder,” without first naming a code-character PVM.

The initially proposed sparse little-o estimate
`sparse-anchor-odd-fourth-moment-is-the-renormalization-gate` is false
before coordinate peeling.  `three-site-pauli-refutes-unpeeled-fourth-moment`
puts `X,X` on one exact face and an external `Z` anchor.  Its common raw
square-function bound is `O(1/L)`, but the sparse fourth moment and anchor
energy are both `Theta(1/L^2)`, so their ratio does not vanish.  The block
is full rank but supported on only three coordinates and is therefore
cheaply repairable, not a far countermodel.

The corrected gate is
`sparse-peeling-before-anchor-fourth-moment-dichotomy`: first use all-dual
tail contraction to assign sparse anchor-odd spikes to a small coordinate
set and repair/shorten those sites at proportional cost; only then seek the
little-o fourth-moment bound on the diffuse shortened core.  This precisely
separates coordinate sparsity from the physical Hilbert-space outlier cut
and identifies the required operator-valued stopping or local repair lemma.
