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

Adding the selfadjoint-contraction equations `X_i^2=I` does not make the
physical cut boundary part of this transverse gap.
`common-character-rotation-is-flat-for-involution-jacobian` rotates two
exact code-character sectors by one common unitary and pinches back to the
old character projection.  Boundary variance is `rho sin^2(2theta)`, while
the involution and every bounded parity residual have squared energy only
`O(theta^4)`; infinitesimally this is exactly the simultaneous-conjugation
kernel of the balanced Jacobian.  The square-root loss is sharp.  However,
for a selfadjoint contraction, sign functional calculus gives
`||X-sign(X)||_2^2<=||I-X^2||_2^2`.  Thus the contraction phase should
gauge away boundary motion and charge sign-rounding cost, rather than seek
a linear Lyapunov for the pre-pinching boundary variance.

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

The first repaired gate,
`sparse-peeling-before-anchor-fourth-moment-dichotomy`, still demanded too
much coherence.  `translated-three-site-blocks-defeat-global-peeling`
averages translated localized Pauli spikes over central summands.  No one
`o(L)` coordinate set catches them, despite an `O(1/L)` correction which
resets three coordinates separately on each summand.

The valid positive half is
`block-adaptive-sparse-reset-is-cheap`: any central measurable family of
coordinate reset sets costs only its trace-weighted density in both
generator displacement and induced balanced energy.  The exact remaining
gate is now `central-adaptive-peeling-or-noncentral-stopping`.  Loewner
layer-cake gives a sparse set in every vector state; one must paste those
sets into central reducing blocks, or prove that their failure to paste
creates a noncentral physical boundary charged by the common covariant
square function.  This is strictly weaker than a global coordinate set and
survives the translated-block counterexample.

The noncentral branch has a rigorous local primitive.
`one-anchor-odd-spike-has-a-cheap-reducing-cut` proves that every
`Y_(a,i)^2` has a spectral threshold whose generator-boundary cost is
`O((q_i+q_a)/t)`.  After cosine--sine block diagonalization, reset `i` on
the high block and retain the operator bound `Y_(a,i)^2<=2t` on its
complement.  What remains is a disjoint-mass or geometrically decaying
stopping selection: cutting all `L^2` spikes independently repeats the same
commutator rows and loses length.

The earlier scalar exponent fence was a bookkeeping error.
`hard-soft-exponent-conflict-is-a-norm-mismatch` notes that the soft
remainder `Ct sqrt(E)` is a row **amplitude**, so it perturbs an amplitude
contraction by the coefficient `Ct`; it need not be `o(E)`.  Fixed small
`t`, or `t=E^alpha` for `0<alpha<1/2`, is compatible with hard reset cost
`E/t^2->0`.  Thus only the reducing-cut summability problem remains, not an
incompatible threshold scale.

The one-cut parity charge is also exact.
`localized-loewner-pays-spike-or-boundary` localizes max-fractional
Loewner order to a spectral cut `p` of `Y_(a,i)^2`: either its boundary
Dirichlet energy is at least `kappa s tau(p)`, or the full anchor row on `p`
is at least `(kappa/4)s tau(p)`.  The latter sums on disjoint reducing
blocks without losing `L`.  The coarea construction has a complementary
`L_1` high-tail bound `(OSC7)`, charging a selected boundary linearly to
`tau(Y^2 1_(Y^2>=t))`.  A greedy ordering must still prevent reuse of that
high-tail mass in successive boundary-heavy cuts.

Global cosine--sine correction is not required for each greedy cut.
`spectral-cut-anchor-reset-pays-boundary-in-one-row` resets only the anchor
on a spectral projection which already commutes with it.  The averaged
generator and parity costs are `O(tau(p)/L)`, while failure of the cut to
reduce the other generators enters only the anchor's complete-pair row at
cost `D(p)/L`.  Thus all static length factors have been removed.  The
remaining dynamic question is whether successive nonreducing resets can
recycle the same boundary energy instead of decreasing the high-tail
ledger.

There is now an exact no-recycling potential for anchor resets.
`odd-spectral-anchor-resets-have-monotone-sign-budget` polarizes the odd
part on every positive spectral cut and proves balanced anchor signs.
Resetting deletes exactly half the cut from the negative spectral
projection; along arbitrary overlapping iterations,
`sum_n tau(p_n)<=2tau(e_-)`.  Thus already spent sign mass cannot be
recreated.  Combined with the fourth-root charge, one cut per anchor per
geometric energy scale is summable.  The last issue is coverage: prove that
this schedule makes every retained anchor-odd part operator-small fast
enough for contraction.

The literal one-shot join is not the correct coverage object.
`orthogonal-odd-cut-join-amplifies-boundary-linearly` gives even orthogonal
site cuts whose join has macroscopic boundary while the anchor and pair
energies vanish.  The dimension-free replacement is
`regularized-anchor-square-function-has-dimension-free-cut`: average the
odd squares first and threshold
`K_a=L^(-1)sum_iY_(a,i)^2`.  Its complement satisfies the exact row-column
bound `qK_aq<=2theta q`, while the cut trace averages as
`O(E_pair/theta)` and its boundary as `O(sqrt(E_pair)/theta)`.  Exact
parity further implies, by
`regularized-anchor-cut-makes-residual-spikes-boundary-heavy`, that every
individual compressed spike remaining below this cut is boundary-heavy.
The aggregate leakage also has an exact safe representation.
`aggregate-cut-compression-stores-boundary-as-involution-defect`
block-compresses every reflection without sign rounding.  The resulting
selfadjoint contractions reduce the cut exactly, retain the same soft
row-column square function, and store both their squared movement and
positive involution residual exactly as `D(p_a)`.  Fixed-width face defects
increase by only `O(D(p_a))`.  The final analytic gate is now the augmented
Newton statement: preserve the linearized gap and nonlinear contraction
for selfadjoint contractions when `I-X_i^2` is included in the energy, and
sign-round only after convergence.
