# Highest-yield remaining attacks: finite-multiplicity reconstruction first

Date: 2026-08-12

## 2026-08-13 exact mass floor: every comb coefficient block is `1/64`

The fixed symbolic block table is complete.  If `F_epsilon` are the four
trace-`1/8` character cuts of the raw-invariant coefficient `C2^2`, then

```text
tau(F_epsilon U* F_eta U)=1/64
```

for all sixteen pairs.  No block vanishes.  See
`TRUE_DOUBLE_PAULI_COMB_IS_FOURIER_FLAT.md` and the exact rational
group-algebra certificate.  Since `||FG||_2^2=tau(FG)` for projections, every
block has a fixed microstate mass floor; the generic identity is Lean-checked.

This trace-flatness is not operator-flatness.  The representative identity
`F G F=(1/8)F` fails exactly, as does its reverse.  Hence the block singular
values can be nonuniform and `(RPC128)` still needs either an actual reduced
Fourier unitary or an invariant spectral truncation with a lower singular
value bound.

This removes positive-density recovery from the final analytic gate.  The
highest-yield theorem is now one-sided finite-multiplicity vanishing: identify
the coefficient multiplication module inside a matrix coordinate and prove
that one orientation of a chosen `F_epsilon`/comb block is `o(1)`, while the
opposite orientation retains `1/64-o(1)`.  `UnitaryProjectionBalance` then
gives the contradiction.  An ambient support or Hall proof cannot work,
because the exact `4 x 4` graph is complete and Fourier-flat.

## 2026-08-13 live bridge: comb blocks of the raw-invariant coefficient

The raw compressor now supplies a canonical positive-density coefficient
`C2^2`, rather than merely another Pauli sign.  With original shifts `X_i`,
raw commutators `C_i=[R,X_i]`, centers `c,d`, and
`A_i=X_i C_i=R X_i R`, the exact relations are

```text
R c R = c d,       R d R = d,
[A_i,Z_i] = c d,   [X_i,C_j]=1.
```

On the `d=-1` carrier, `R` swaps the two `c` sheets.  The splice

```text
B_i = ((1-c)/2) A_i + ((1+c)/2) X_i
```

is a raw-fixed coefficient involution commuting with the Pauli coordinates.
See `TRUE_RAW_DOUBLE_PAULI_COEFFICIENT_PACKET.md`; the finite atlas audit and
generic Lean certificate are checked.

The highest-yield next calculation is no longer abstract radical-quotient
recovery.  It is the fixed symbolic block table of `U* B_i U` relative to the
joint `c,d,B_0,B_1` character cuts.  Success means deriving the transported
carrier containment required by `PauliBranchTransfer`, or the three
contraction products in `LeavittTraceFloor`.  Failure means exhibiting the
resulting finite comb closure explicitly.  Do not retry a single transported
sign: `FALSE_COMB_TRANSPORTED_SIGN_STAYS_FINITE.md` proves that route remains
inside a finite order-32 cell.

## 2026-08-13 exact endpoint: one transported-carrier containment

The two finite branch operators are now exact:

```text
E=P Q,       T0=U* P Q,       T1=U* R P Q.
```

They have common initial `E`, orthogonal ranges, and range sum `U* Q U`.
The traces are `tau(E)=1/8` and `tau(Q)=1/4`.  Therefore the single
containment `U* Q U <= E` gives the desired contradiction immediately.
See `TRUE_PAULI_BRANCH_TRANSFER_PACKET.md`; every operator identity is
Lean-checked in `Sofic/PauliBranchTransfer.lean`.

Do not attempt to derive this containment pointwise on additive root
characters.  The implication is false: `ef=f` gives
`ell(ef)=ell(f)`, not `ell(f)=1 => ell(e)=1`.  The highest-yield remaining
calculation is to construct the finite paired radical quotient on which
multiplication by `e` really acts as identity on the `f` range, then prove
the raw compressor identifies its positive-density carrier with the Pauli
cut `E`.

## 2026-08-13 narrowing: star is closed; multiplication-to-support remains

The finite star-synchronizing extension is now proved hyperlinearity-neutral.
For an involution `psi`, two-sheet block matrices prove
`Q semidirect_psi C2` hyperlinear if and only if `Q` is.  See
`TRUE_INVOLUTIVE_STAR_EXTENSION_PRESERVES_HYPERLINEARITY.md` and the
Lean-checked identities in `Sofic/InvolutiveTwoSheet.lean`.

This removes star/adjoint compatibility from the attack list.  The raw
compressed carrier, trace-half coefficient cut, synchronized star, and exact
finite branch Pauli cell are all available.  The single highest-yield atlas
question is now whether the cross-root Steinberg multiplication relations
force the ring identity `ef=f` to become support containment between those
finite coefficient cuts.  Any proof that only uses ambient finite-subgroup
spectral projections is already ruled out by the balanced finite chart; the
new argument must recover a coherent finite radical quotient or equivalent
matrix-coordinate character completion.

## Revised decision

The active construction target should no longer be another deformation of the
fixed inner-aligned Leavitt atlas.  The signed group-algebra identity

\[
d_{11}\in \sum_z k[A_8]d_z+
\sum_{s,g}k[A_8](g-1)d_s
\]

holds over every field.  It eliminates, in one stroke, every fixed-fold
square-zero construction on every finite-dimensional module, including
indecomposable modules, arbitrary multiplicities, and off-diagonal couplings.
Changing the characteristic or module is therefore dead work.

The relative-perfectness audit has now exposed a different, genuinely
matrix-specific atlas route.  The boundary group has both a classical
amalgam branch and a distant exact Leavitt branch, so arbitrary tracial or
group-theoretic alignment is false.  But in a canonical matrix microstate the
regular finite chart has a finite multiplicity algebra, whereas the exact
Leavitt regular model has an infinite coset multiplicity algebra.  The
highest-yield immediate gate is therefore:

> Fourier-compress the fixed order-eight root Heisenberg subgroup, take the
> Pauli blocks of the already explicit raw compressor words, and determine
> whether the full atlas identities force a binary Leavitt family in the
> finite multiplicity algebra.

This is a fixed symbolic block calculation.  If it succeeds, the elementary
matrix trace floor gives a uniform atlas gap and proves the Leavitt group
nonhyperlinear.  If an exact finite model or a missing block identity refutes
it, the route can be killed quickly.  The exact theorem and falsification
gates are in
`ATLAS_RELATIVE_PERFECTNESS_AND_COEFFICIENT_ENDPOINT.md`.

There is now a strictly smaller success condition.  A unitary over a finite
tracial coefficient algebra has equal leakage in both directions across
every projection cut.  Summing over a four-step flag shows that its total
upper-triangular block mass is at most three times its lower-triangular mass.
Hence it suffices to force the comb compressor to be approximately upper
triangular in a finite Fourier/parabolic multiplicity corner while retaining
one upper block with positive normalized mass.  This finite flag-support
extraction `(RPC42)` uses unitarity as the missing additive identity and
avoids reconstructing all four Leavitt operators.  It is now the first atlas
gate to test.

In fact, one cut is enough.  With the rank-three-versus-one coordinate
projection `P=diag(1,1,1,0)`, the comb has zero lower-left corner and an
upper-right corner containing `p_1`.  Every unitary over a finite tracial
coefficient algebra satisfies

\[
 \|(1-P)WP\|_2=\|PW(1-P)\|_2.
\]

Thus the sharp first gate is `(RPC47)`: extract one finite-multiplicity
projection cut, make the forbidden leakage tend to zero, and certify fixed
positive leakage in the opposite direction.  Four sectors and a complete
Leavitt-family reconstruction should only be attempted if this one-cut
recipe cannot be obtained.

Before attempting even that positive-mass estimate, test the support-only
Hall gate `(RPC43)`.  If a root-character compression forces a collection
of source sectors to land in target sectors of strictly smaller total
weight, unitarity gives a fixed forbidden-block lower bound immediately.
The bare four-coordinate comb graph is Hall-balanced, so any such deficit
must arise only after Pauli/root-sector compression; this is a fast and
decisive falsification test.

The Hall projections must live in the finite coefficient/multiplicity
algebra after canonical regular-chart disintegration.  A graph made only
from ambient finite-subgroup spectral projections is impossible: its exact
support relations also hold in the finite tracial algebra `L(Q)`, where
unitary conjugacy and trace already enforce the weighted Hall inequality.

The cleanest way to remove the commutant-gauge ambiguity is categorical.
Exactify one fixed finite subgroup `F` in both chart restrictions and write

```text
H_n = direct_sum_(sigma in Fhat) V_sigma tensor K_(sigma,n).
```

The blocks of a relative chart intertwiner are arrows between the finite
multiplicity spaces `K_(sigma,n)`.  Changing the regular-chart tensor
identification acts only by change of basis at the vertices.  Thus ranks,
singular values, kernel dimensions, and incidence of the block arrows are
gauge-invariant data of a finite quiver representation.  The immediate
symbolic target is to reduce the raw compressor and adjacent-root relations
to either

```text
K -> L <- K
```

with two asymptotically isometric arrows having asymptotically orthogonal
ranges, or to a weighted Hall-deficient subquiver.  Either conclusion gives
a dimension-vector contradiction in finite multiplicity.  In the exact
Leavitt branch the corresponding Hilbert multiplicity spaces are infinite,
so the same algebraic arrows can be proper isometries and there is no
contradiction.  This quiver formulation is the gauge-free version of the
finite gauge-index theorem: search for invariant arrow-rank identities, not
for zero entries of one arbitrarily gauged `20160`-by-`20160` block matrix.

The multiplicative success condition is now smaller than full Leavitt-family
or two-column reconstruction.  If four extracted coefficient blocks are
contractions and approximately satisfy

```text
T_0 S_0 = 1,     T_1 S_1 = 1,     T_0 S_1 = 0,
```

then their maximum normalized-HS defect is at least `2-sqrt(3)>1/4`, uniformly
in the matrix size.  The proof uses only trace Cauchy--Schwarz, positivity of
Gram deficiencies, and the fact that an approximate right inverse makes a
contraction almost full-rank.  It is formalized in
`Sofic/LeavittTraceFloor.lean`.  Thus the
additive relation `S_0T_0+S_1T_1=1` need not be extracted at all.  The live
Pauli calculation should target these three products, which occur in the
Steinberg commutators
`[x_12(t_i),x_23(s_j)]=x_13(t_i s_j)`.  See
`(RPC108)--(RPC119)`.

Do not treat that commutator packet as the extraction itself.  The
extraspecial group of order `32` has a left-regular two-qubit Pauli model in
which the four commutators give exactly the table `delta_ij` and every
nonidentity packet element has trace zero.  On its negative central sector
the labels act on the Pauli factor and do nothing on the multiplicity
factor.  Thus the missing step is specifically a raw-compressor relation
which resolves the many-to-one extension fibers of the dual corner maps
`ell |-> ell o (a |-> s_i a t_i)` and turns the resulting arrows into
endomorphisms of one finite multiplicity space.  Finite Clifford normalizers
of the Pauli packet remain exact countermodels.  See `(RPC120)--(RPC124)`.

The gauge-free target can be stated exactly in terms of the pairing
`b_ell(a,b)=ell(ab)`.  Its left radical is a right ideal and its right
radical is a left ideal, so `a|->a t_i` and `b|->s_jb` act on the two radical
quotients.  They satisfy
`b_ell(a t_i,s_j b)=delta_ij b_ell(a,b)`.  On finite nondegenerate quotients
the two diagonal identities make the relevant arrows bijective, while the
cross identity makes the whole pairing zero.  Thus the live analytic theorem
is a robust radical-quotient extraction from the raw compressor packet, not
an arbitrary choice of regular-chart coefficients.  The analytic pairing
must be unitary (Fourier-flat), not merely invertible: an uncontrolled
condition number destroys any dimension-free defect estimate.  With a
unitary pairing `U`, the three desired defects are
`R_0^* U L_0-U`, `R_1^* U L_1-U`, and `R_0^* U L_1`; multiplying on the right
by `U^*` gives the contraction packet formalized by the `2-sqrt(3)` gap.  A
spectral truncation may replace flatness only after proving uniform lower
singular-value, arrow-invariance, and positive-trace estimates.  See
`(RPC125)--(RPC129)`.

The unitary here is the normalized Fourier transform of the perfect
`F_2`-pairing, not its `0/1` bilinear-form matrix.  The cross identity gives a
rank-one constant Fourier kernel; it becomes zero only on the reduced Fourier
spaces obtained by deleting the constant source mode and the target delta
mass at zero.  Consequently the extraction must additionally prove that the
approximate coefficient arrows are near-bijective and that these
codimension-one modes can be removed with negligible invariant leakage.
Treating algebraic nondegeneracy as a complex unitary, or treating the cross
kernel as literally zero before this reduction, is invalid.

A gauge-free variant is now equally high priority: exactify a finite binary
root subgroup and track its atomic character multiplicities.  The correct
vector is the square root of the multiplicity distribution, so property
`(T)` acts through Hellinger distance.  A dimension-free gap would follow
from an honest compressor action on the character labels with no finite
nontrivial orbit, provided normalized-HS covariance controls the Hellinger
displacement.  The diffuse invariant Haar measure in the exact Leavitt
trace is not an `ell^2` counting vector, so it does not refute this
matrix-specific gap.  However, the actual compressor acts by the proper
embedding `a |-> s_0 a t_0`; its dual is many-to-one rather than a
permutation.  The finite Hellinger estimate is valid, but the naive
property-`(T)` permutation argument is not.  A revival needs a
transfer-operator gap using additional atlas relations.  The
compressor-only transfer gap is actually false: evaluation at the constant
path `000...` gives a nontrivial additive character fixed by
`a |-> s_0 a t_0`.  Do not pursue the empirical-character route without
first exhibiting an additional relation which moves this fixed character.
See `(RPC59)--(RPC73)`.

The overlap quiver has now been reduced further by exact character theory.
The subgroup `H=diag(GL_3(2),1)` is the stabilizer of a nonincident
point--hyperplane flag, and

```text
Ind_H^A8(1) = 1 + 2(14) + 35 + 56.
```

Thus its spherical commutant has dimension seven, and the only non-scalar
representation-type gauge is one `2 x 2` block on the repeated
14-dimensional constituent.  The 35 and 56 sectors are multiplicity-one
scalar channels.  However, the proposed direct scalar-sector test has now
been killed exactly: in the classical amalgam `A8 *_H A8`, the compiled raw
swap and comb both reduce to the identity, while the hard class-11 prefix
and next letter reduce to elements of `H`.  Therefore none of the four
elements carries a nontrivial closed holonomy on the aligned spherical
module, in the scalar sectors or the 14-doublet.  See
`FALSE_CLASSICAL_SPHERICAL_RAW_PACKET_COLLAPSE.md`.

The same collapse certificate has a positive quantitative use.  All twelve
second-chart letters of the 25-syllable raw word lie in `H`, and replacing
them by first-chart letters makes the word exactly trivial.  Telescoping
therefore gives `||r_src(U)-1||_2 <= 12 Delta_H`.  Since `r_src` is a
nonidentity group element, tracial separation forces
`Delta_H >= sqrt(2)/12-o(1)` and hence the explicit Reynolds deficit
`1-||E_H(U)||_2^2 >= 1/13440-o(1)`.  The sharper constant uses the fact that
the twelve replacements are eight and four copies of only two `H`-elements,
so their squared displacement sum is at least `1/40-o(1)`.  The live nonlinear calculation may now
exclude a fixed tube around the aligned fold.  See
`TRUE_RAW_WORD_REYNOLDS_GAP.md`.

Those two `H`-elements generate the six-element subgroup
`K=GL_2(2)~=S3`.  Its Reynolds projection satisfies the substantially
stronger localized bound `1-||E_K(U)||_2^2 >= 1/480-o(1)`.  Therefore the
next coefficient calculation should first use the three `S3` types
`1,sign,2`, retaining the hard-pair child labels through their block
products.  Expanding immediately to all `H`-types is unnecessary unless
this three-vertex quiver provably forgets the cross branch.

Exact subgroup closure makes this localization structural.  The four
first-chart raw letters generate a commuting `S3`, so the entire raw word
lies in an `S3*S3` transport cell and the classical fold is `S3 x S3`.
Each class-11 hard element extends the raw `S3` to an `S4`; the two distinct
extensions generate `GL3(2)` of order 168.  The minimal live quiver is thus
`S4 <- S3 -> S4`, with the caveat that the running hard prefix is a
cross-chart product whose first `S4` must be recovered rather than assumed.
See `TRUE_RAW_WORD_S3_TIMES_S3_LOCALIZATION.md`.

The complex branching matrix for `S4 -> S3` is multiplicity-free, but its
regular dimension vector is exactly balanced: one regular `S4` restricts to
four regular `S3` representations.  Hence type incidence alone cannot
produce Hall deficiency.  The live invariant is a closed product, singular
value, or kernel of the actual multiplicity arrows through the standard
`S3` channel, where three `S4` extension types meet.  See
`FALSE_S3_S4_TYPE_ONLY_HALL_DEFICIT.md`.

There is now a canonical positive-density carrier for the nonlinear block
calculation.  In characteristic two the raw word is a nontrivial involution
which centralizes the compressed core.  Hence every hypothetical
trace-preserving hyperlinear model contains
`e=(1-r)/2` in the compressed-core commutant with trace exactly `1/2`.
Writing `C=Core'` and `D=alpha(Core)'` gives
`C subset D=uCu*`, with `e in D` and `u*eu in C`.  This does not by itself
recover finite-coordinate commutants, but it removes the vanishing-rank and
XOR-projection issues for the carrier cut.  See
`TRUE_RAW_INVOLUTION_SPECTRAL_CUT.md`.

The carrier now lands in the correct finite coefficient factor.  The raw
involution centralizes the compressed order-eight root Heisenberg group
`H_0`, lies outside it, and generates `H_0 times C2`.  On the central
`Z=-1` Pauli sector it therefore acts as `I_2 tensor r_hat`; its negative
cut is a projection in the Pauli multiplicity algebra with relative trace
exactly `1/2`.  The remaining bounded task is to compute the comb/hard
transport on that same coefficient cut and obtain one-way leakage.  See
`TRUE_RAW_PAULI_COEFFICIENT_CUT.md`.

The complete finite branch cell is now identified.  The compressed root
Heisenberg group and the complementary pair generated by the raw word and
`x_13(p_1)` form `D8 times D8` of order `64`.  For the hard cylinder signs,
`<r,x_13(p_11),x_13(p_001)>` is `D8 times C2`.  On its joint negative
sector, the two raw arrows are exact and orthogonal, but two trace-`1/8`
ranges merely fill a trace-`1/4` carrier.  The sole missing operation is now
coefficient multiplication-to-support: recover
`p_child p_parent=p_child` as spectral containment in the finite
multiplicity algebra.  See `TRUE_RAW_BRANCH_PAULI_CELL.md`.

The raw swap and comb are now also explicit in the two-chart source: exact
Steinberg compilation gives reduced words of lengths `25` and `175` in
`A8*A8`, verified against their scalarized Leavitt values.  Hence the
spherical-sector test no longer needs to treat their printed ring matrices
as if those entries were already available in a unitary microstate.  Use the
encoded words in `atlas-raw-compressor-source-words.json`.  Their exact
classical collapse shows that they must be evaluated before projection to a
fixed aligned flag module: the remaining gate is nonlinear coefficient
recovery on the Reynolds-misaligned branch, followed by gauge-invariant
quiver compression.  See `TRUE_RAW_COMPRESSOR_TWO_CHART_SOURCE_WORDS.md` and
`FALSE_CLASSICAL_SPHERICAL_RAW_PACKET_COLLAPSE.md`.

Do not search the current radius-five collision tree for a single linear
Hecke edge.  The exact archived scan has no word with exactly one transverse
second-chart syllable, hence no direct equation `W A = B W` after
`H`-exactification.  The support graph must be derived from quadratic or
higher block equations (or from a genuinely new relation packet).

Likewise, do not obtain the Hall graph from central root projections and one
compressor alone.  At every finite binary depth, each source character is
connected to all sign extensions on the unused subtree, and the total trace
weight of those extensions equals the source weight exactly.  The graph is
weighted-Hall-balanced.  The first meaningful support calculation must
include block coefficients of the raw second compressor and adjacent
noncentral roots, which are the only displayed relations coupling the two
subtrees after disintegration.

The same closure now holds for atomic Hellinger arguments on every finite
additive coefficient window, not merely at every diagonal depth.  Given a
finite-dimensional `K<=(L,+)` and a finite word radius, take the span of
its orbit under the injective maps `a|->s_iat_i`.  Each partially defined
corner injection extends by basis completion to an automorphism of that
finite span.  Averaging over the dual gives an exact finite atomic model
with regular Fourier character on the entire window and exact local
compressor covariance.  Therefore no fixed package consisting only of
additive root moments and injective linear compressor transport can yield a
Hellinger gap.  Increasing root depth or adding more additive coefficients
is dead work; the next calculation must use coefficient multiplication,
cross-root commutators, or noncentral/Pauli relations.  See
`(RPC85)--(RPC107)`.

The best independent fallback is:

> Start with one fixed finite synchronous BCS/CSP game which has a perfect
> commuting-operator strategy but a uniform gap for finite-dimensional
> strategies, and construct a bespoke finite LCS game preserving those two
> properties.

No efficient or uniform compiler is sought.  Only this one source algebra has
to be linearized.

## Exact target theorem

Fix a finite synchronous BCS game \(B_0\) satisfying

\[
\omega_{qc}(B_0)=1,
\qquad
\omega_{qa}(B_0)\le 1-\eta
\tag{HL1}
\]

for some \(\eta>0\).  The negative solution of Connes embedding/MIP*=RE
supplies a finite game separation.  Gate 1 below is to pass one such game
through the current BCS/CSP reductions and verify, in one finite
presentation, that synchronous or oracularizable perfect completeness and a
constant finite-dimensional soundness gap are retained.  Those ingredients
exist separately in the literature; their exact composition for our chosen
instance must not be assumed without replaying it.

Construct a finite binary linear constraint system \(L_0\) and constants
\(c,C>0\) with:

1. **exact completeness:** every perfect commuting strategy for \(B_0\)
   induces a perfect commuting strategy for \(L_0\);
2. **robust soundness:** a finite-dimensional strategy for \(L_0\) of defect
   \(\delta\) induces a finite-dimensional strategy for \(B_0\) of defect at
   most \(C\delta^c\).

Then

\[
\omega_{qc}(L_0)=1,
\qquad
\omega_{qa}(L_0)<1.
\tag{HL2}
\]

The solution group of \(L_0\) has its distinguished central involution
nontrivial in a commuting representation but trivial in every asymptotic
matrix representation.  The standard LCS solution-group correspondence then
produces a nonhyperlinear group.

### The final solution-group implication is profile-free

For completeness, no faithfulness or positive-rank hypothesis is hidden in
the last sentence.  Let `Gamma(A,b)` be the binary LCS solution group and
let `J` be its distinguished central involution.  If

\[
 \omega_{qc}(A,b)=1,
 \qquad
 \omega_{qa}(A,b)<1,
 \tag{HL2a}
\]

then `Gamma(A,b)` is nonhyperlinear.

Indeed perfect commuting completeness makes `J` nontrivial in the solution
group.  If the group were hyperlinear, choose a homomorphism

```text
pi:Gamma(A,b) -> product_omega M_(d_n)
```

into a normalized tracial matrix ultraproduct which separates `J`.  Since
`J` is a central involution,

\[
 q={1-\pi(J)\over2}
 \tag{HL2b}
\]

is a nonzero central projection.  Lift `q` to matrix projections, compress
all unitary lifts to their ranges, normalize the corner traces, and polar
correct.  The resulting approximate representations still have vanishing
normalized-HS multiplicative defect and now satisfy

\[
 J\longmapsto-I
 \tag{HL2c}
\]

in normalized Hilbert--Schmidt norm.  The usual LCS
approximate-representation/strategy construction therefore gives
finite-dimensional strategies whose winning probabilities tend to one.
This contradicts `omega_qa<1`.

The corner may have vanishing relative rank in the original matrices; its
trace is renormalized after compression.  Thus the only unproved issue in
this lane is the existence of `(HL2a)`, not conversion of such an instance
to a nonhyperlinear group.  This is also why the `epsilon=0` endpoint in
Taller--Vidick is exactly the group-theoretic open problem.

## Why this target is narrower than the published open problem

Taller--Vidick prove RE-hardness for LCS games with completeness
\(1-\epsilon\), and explicitly note that \(\epsilon=0\) would imply a
nonhyperlinear group.  Their completeness loss comes from deliberately added
noise in the distorted long-code test.  They also explain two barriers to a
generic perfect-completeness compiler:

* an efficient classical compiler would imply \(P=NP\);
* not every BCS algebra admits a morphism into an LCS algebra.

Neither barrier rules out the target above.  It is nonuniform, may be enormous,
and concerns one specially chosen non-CE algebra.  We should therefore avoid
trying to repair the noisy long-code test and instead test direct algebraic
linearizability of this single instance.

There is now also an exact mask-distribution no-go.  Perfect completeness
forces the mask to equal `1` on the support of the honest assignment PVM, so
the Fourier coefficients supported there are completely undamped.  Putting
noise only outside that support leaves a decoder of size at most the source
projection game's random-guessing floor; adding a correction answer accepts
all high-degree Fourier characters exactly.  See
`FALSE_PERFECT_COMPLETENESS_MASK_NO_GO.md`.  Thus the missing theorem cannot
come from retuning the noise or adding one more linear mask variable.

## First decisive gates

### Gate 1: freeze a finite source presentation

Extract from a current synchronous BCS/CSP MIP*=RE reduction one explicit
finite source \(B_0\), together with the two replayable implications in
`(HL1)`.  Record its projection generators, partition-of-unity relations,
local commutation relations, and forbidden products.

### Gate 2: exact LCS-algebra embedding test

Attempt to encode each source projection by a word in involutions of a finite
solution group, with the source partition and forbidden-product relations
holding identically.  This is an exact finite word problem.  The first search
should allow auxiliary variables and equations freely; efficiency and size do
not matter.

Kill the route immediately if a representation-theoretic invariant of the
specific \(B_0\) rules out every such encoding.  The generic obstruction is
not enough.

### Gate 3: robust reverse decoding

For a candidate exact encoding, prove a normalized-HS decoding estimate from
near-perfect LCS strategies back to near-perfect \(B_0\) strategies.  Use:

* HS stability of projection and involution relations;
* local commutativity gadgets;
* Paddock's dimension-independent BCS strategy/approximate-representation
  correspondence;
* finite telescoping only.

This gate must be dimension independent.  No bounded-dimension scan is a
substitute.

### Gate 4: solution-group extraction

Once `(HL2)` is certified, write down the finite solution-group presentation
and verify the distinguished central involution is visible in the commuting
model and uniformly invisible in matrices.  This is the final
nonhyperlinearity proof.

## Resource allocation

Stop:

* large-\(k\) unitary optimization;
* new characteristics or finite-field modules;
* fixed-fold first-order, Jordan, or off-diagonal variants;
* natural-overgroup scans beyond the completed \(A_9/A_{10}\) audit;
* generic perfect-completeness long-code repair.

Prioritize the Leavitt atlas only at the finite-multiplicity reconstruction
gate: the order-eight Heisenberg Fourier corner, the two raw compressor
blocks, and the smallest boundary-plus-interior packet.  Do not resume blind
large-\(k\) optimization or first-order deformations.

Retain the one-instance perfect-linearization program as the independent
fallback.  It starts with a known finite non-CE separation, but its missing
perfect-completeness compiler is broader and currently less tied to a fixed
symbolic identity than the compressor-block gate.

## Probability assessment

These remain attacks on a famous open problem.  Neither endpoint is close to
proved.  The finite-multiplicity route has the best immediate falsifiability
because its next claim concerns fixed blocks of explicit words; the
one-instance linearization route has the stronger external source separation
but a less explicit missing compiler.
