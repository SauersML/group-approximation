# Uniform unitary expanders and the nonhyperlinear-group goal

The September 1 preprint by Anshu, Balasubramanian, Haferkamp, Harrow, and
Tan, [Depth-1 expanders on the unitary group and applications,
arXiv:2609.01605v1](https://arxiv.org/html/2609.01605v1), supplies a new
dimension-uniform resource.  Theorem 2.17 gives 25 explicit generators of
`SU(2^(3s))`, built from Clifford circuits and T gates, with a uniform gap
over all finite-dimensional continuous unitary representations.  Its
Definition 1.3 takes the gap only on the complement of invariant vectors.
The paper's Outlook explicitly leaves device-independent authentication
of its CNOT observables as a further problem.

This audit tests two direct uses toward nonhyperlinearity.  Neither works.

## A stronger gap does not remove the multiplicity twist

`all-representation-expansion-keeps-macroscopic-multiplicity-swap` proves
that diagonal checks `V_i tensor V_i` have an exactly invariant swap `F`
with

```text
dist_2(F,I_d tensor M_d)^2=1-1/d^2.
```

This is a strengthening of the existing normalizer-twist obstruction: its
mass does not disappear as the old spin dimension grows.  The stronger gap
in the new paper is fully consistent with the example because the swap
belongs to its invariant subspace.  It therefore does not repair
`uniform-relative-clifford-tape-cell` or the commutant normalization input
to the nonhyperlinear-group route.  One must still derive checks acting
trivially on multiplicity, or another argument that controls those
correlated invariant operators.

## The direct matrix-family group is residually finite

Let `V_i^(s)`, `1<=i<=25`, be the paper's explicit tuples and form the
ordinary discrete group

```text
H=< (V_i^(s))_(s>=1) : 1<=i<=25 >
   <= product_(s>=1) SU(2^(3s)).
```

This group is residually finite.  Here is an explicit separation argument,
which does not assume that the whole infinite product is linear.

For `1!=h in H`, choose a coordinate `s` in which `h_s!=I`.  All entries
of the finitely many generators and their inverses at this coordinate
are algebraic: Clifford and T gates have algebraic entries, as do their
finite products and tensor products.  Choose a number field `K` containing
them and an integer `c>=1` clearing their denominators.  The coordinate
group lies in `GL_D(O_K[1/c])`, where `D=2^(3s)` and `O_K` is the ring of
integers of `K`.

A nonzero entry of `h_s-I` has form `b/c^k`, with `0!=b in O_K`.  Choose
a rational prime `ell` not dividing `c N_(K/Q)(b)` and a prime ideal
`mathfrak p` above `ell`.  The residue field `O_K/mathfrak p` is finite;
`c` and `b` remain nonzero in it.  Reducing every generator and its inverse
modulo this ideal defines a homomorphism from the coordinate group to a
finite general linear group, and the image of `h_s` is not the identity.
Composition with the coordinate projection separates `h` in a finite
quotient of `H`.

Finite products of these quotient maps separate every prescribed finite
set.  Their left regular permutation representations are exact
homomorphisms and have normalized trace zero at the separated nonidentity
elements.  Thus `H` is sofic and hyperlinear.

This argument concerns the direct diagonal subgroup in the *ordinary*
product.  It does not assert the same for a tracial metric-ultraproduct
quotient, where coordinate evaluations need not descend, or for an
additional quotient or HNN extension.  Those operations need their own
proofs.

## A localization lemma that does survive multiplicity twists

The separate claim
`two-pauli-anchors-localize-arbitrary-normalizer-twists` supplies a positive
relative estimate.  On an exact old `n`-qubit factor, expand a matrix in
its Pauli basis and apply the classical expander gap to the scalar norms
of its coefficient matrices.  Arbitrary multiplicity conjugations preserve
these norms.  Two coordinate Pauli commutators detect at least half the
mass in each nonidentity label orbit.  Together these facts bound distance
to the old factor's commutant, uniformly in multiplicity and qubit count.

The argument needs no multiplication relations among the multiplicity
unitaries.  Approximate coordinate covariance can be rounded separately
for each normalizer, in the original dimension.  Its error is measured by
the sum over all `2n` coordinate rows; a uniform bound on each row incurs
a `sqrt(n)` loss.  Thus this removes the full actor-table exactification
requirement from the localization step, but does not give bounded
presentation area for the needed rows or construct the exact old factor.

## Consequence for the active goal

The next exact syntax check is now complete in
`anchored-pauli-extension-splits-off-its-payload`.  For an actor `Q` acting
on one finite Pauli frame, the two anchors and actor commutation relations
force every payload generator to centralize that entire frame.  With only
internal payload relations, the universal group is exactly
`(P_n semidirect Q) times L`.  It embeds in the product of one finite group
with `Q times L`; therefore it is hyperlinear precisely when both inputs
are.  In particular free or finite actors and free payloads give exact
finite-quotient canonical microstates, with no relator energy to charge.
The new localization estimate must therefore be followed by a mixed
relation absent from this presentation, rather than by more deductions
from the same centralizing checks.

The constant-depth Schur target also needed an explicit hypothesis:
its positive base floor is required only on tuples with
`||w(V)-I||_2>=rho`, for a fixed `0<rho<sqrt(2)`.  Without this restriction
the trivial representation contradicts the proposed contraction at zero
energy.  The corrected statement and its root route retain the original
endpoint because canonical microstates of a nonidentity word have squared
marked distance tending to `2`.

The new theorem improves available expander constructions but proves no
nonhyperlinear discrete-group witness.  The two direct attempts above have
explicit failures, not merely an absence of a cited theorem.  The remaining
work is still to derive a dimension-independent obstruction from one
group's actual microstate relations, including its multiplicity action.
The Cairn root `non-hyperlinear-group` remains OPEN.

## Validation scope

The [Cairn replay report](nonhyperlinear-cairn-replay-2026-09-04.json)
records edited-source lint and graph compilation against the existing
cached nodes, with ten explicit source overlays.  This ran on MSI acn116
in 1.252 seconds with no errors and three existing dependency-cycle
warnings.  Both new lemma routes compile as COMPLETE; the root and the
uniform relative-cell claim remain OPEN.  This is not a full source
rebuild or a proof-kernel verification of the mathematical arguments.

The subsequent [fixed-frame syntax replay](anchored-pauli-syntax-replay-2026-09-04.json)
includes fourteen source overlays and the new direct-product result and
separation correction.  It ran on the same node in 1.448 seconds, with no
errors and the same three existing cycle warnings.  The direct-product
route compiles as COMPLETE; the corrected constant-depth target and the
nonhyperlinear-group root remain OPEN.  Its validation scope has the same
cached-source and non-kernel limitations as the earlier replay.
