# Research agenda (owned and maintained by the formalization side)

Started 2026-08-08. This is my program for the universal-hyperlinearity and
hyperlinear-versus-sofic frontiers, maintained across sessions.  The primary
target is an explicit nonhyperlinear group; the radical-collision program is
the parallel route to a hyperlinear nonsofic group.  Doctrine: every claim is
kernel-checked, cited from a source, or explicitly conjectural.

### 2026-08-14: path-shaped PVM classicalization has no outcome loss

For finite PVMs `P,Q`, compress `Q_j` into every `P_i` corner and apply
cardinality-free POVM orthogonalization there. This keeps `P` fixed and
produces a commuting PVM `Q'` with

```text
sum_j ||Q'_j-Q_j||_2^2
 <=5 sum_(i,j)||[P_i,Q_j]||_2^2.
```

Applying this successively along `L0--R0--L1--R1` makes all three required
edges commute exactly with universal error bounds, even when the map-outcome
sets grow. Moreover, for exact finite abelian root representations, the
total character-PVM commutator energy equals the full subgroup-averaged
unitary commutator defect by Parseval. See
`TRUE_PATH_PVMS_CLASSICALIZE_WITHOUT_OUTCOME_LOSS.md`.

Thus simultaneous PVM rounding is closed. The live gate is to construct the
whole-map decoder and prove vanishing total commutator energy plus the three
Leavitt multiplication mismatch rates for its path edges.

### 2026-08-14: commuting target packets synchronize transition PVMs

For one common source projection `P` and two target PVMs `E,F`, the
transition POVMs `P E_i P` and `P F_j P` satisfy a cardinality-free total
commutator bound. Its square root is at most

```text
sqrt(target commutator energy)
 +sqrt(E leakage/2)+sqrt(F leakage/2).
```

Individual de la Salle rounding preserves vanishing total commutator energy,
again without an outcome-count loss. See
`TRUE_COMMUTING_TARGET_PACKETS_SYNCHRONIZE_TRANSITIONS.md`. Therefore the
multi-edge analytic gate closes if the raw/four-root packet routes the three
required pairs to commuting target root packets on common source carriers.
The remaining audit is now algebraic/geometric: verify such placements and a
multiplication-coherent decoder, or produce an exact countermodel showing
that the atlas cannot supply them.

### 2026-08-14: commuting outer roots retain the Leavitt product

The needed distant-root placement is exact. The packets

```text
x_12(a t_i),   x_34(s_j b)
```

commute, while the fixed middle root gives

```text
[x_12(a t_i),[x_23(1),x_34(s_j b)]]
 =x_14(delta_ij a b).
```

This is documented in
`TRUE_COMMUTING_OUTER_ROOTS_RETAIN_LEAVITT_TABLE.md` and stated source-first
in `Leavitt/OuterRootLeavittRouting.lean`. It removes the local Pauli
noncommutation from the three path contexts without losing the two
diagonal-one and two cross-zero identities.

The long root commutes with both outer packets and the middle root, so its
nontrivial spectral cut is already an exact common positive-density carrier.
The finite `UT_4(F_2)` regular model nevertheless realizes this carrier and
the full nested table without a classical decoder. See
`TRUE_LONG_ROOT_CARRIER_IS_COMMON_BUT_NOT_A_DECODER.md`.

The live theorem is therefore the **proper-compressor** outer-root decoder:
use growing extension-fiber covariance, not merely the finite four-root
packet, to make the outer transition blocks deterministic and transfer their
labels to the long-root character with vanishing total mismatch.

### 2026-08-14: one comb compressor gives one joint outer PVM

In rank five, place the complete four-root chain in the rank-four core. The
same comb compressor then implements `alpha(a)=s_0 a t_0` on both commuting
outer root groups. Exactify their product group and apply covariance once to
`alpha x alpha`. If the two marginal RMS defects are `e_L,e_R`, the joint
defect is at most `e_L+e_R`, so one joint extension-character PVM is obtained
with total rounding error below `9(e_L+e_R)^2`.

The two outer transition measurements are exact coarsenings of this one PVM;
there is no remaining PVM synchronization or marginal-matching gate. See
`TRUE_ONE_COMPRESSOR_JOINTLY_RECOVERS_BOTH_OUTER_TRANSITIONS.md`.

The live theorem is now the finite-window endomorphism decoder: extract from
the joint outer characters common finite paired-radical label spaces on
which the four one-sided Leavitt maps act with vanishing boundary and pairing
error.

### 2026-08-14: covariance closes total single-edge transition variance

`TRUE_COVARIANCE_CONTROLS_TOTAL_TRANSITION_VARIANCE.md` corrects the apparent
fine-fiber gate. Conjugating the explicit source Fourier cut by the actual
unitary compressor puts it within the covariance RMS defect of the entire
coarse target Fourier cut. That cut is a sum of fine extension-character
cuts, so

```text
sum_zeta ||[U P_chi U*,Q_zeta]||_2^2
 <=2 (covariance RMS defect)^2.
```

The intrinsic effects therefore round to a fine-outcome PVM with total error
below nine times the squared covariance defect, independent of all fiber
sizes. Positivity, source gauge, and single-edge measurement recovery are
closed. The live theorem is multi-edge multiplication compatibility of the
separately recovered PVMs; the finite Pauli model shows that separate exact
measurements need not be jointly classical.

### 2026-08-14: two coarse branch partitions recover the fine PVM

`TRUE_TWO_COARSE_PARTITIONS_RECOVER_FINE_CHARACTER_PVM.md` proves a
cardinality-free refinement lemma. If finitely many coarse maps on a fine
PVM are jointly injective, the fine block-diagonal expectation is the
composition of their coarse expectations, and

```text
D_fine(T) <= sum_i D_i(T)
```

with constant one. Because the compressor is the corner map
`a |-> s_0 a t_0`, the relevant additive decomposition has four corners.
Actual-unitary covariance already recovers the fine PVM on each single edge;
the lemma is now the endpoint for combining compatible corner-label PVMs
across multiple adjacent-root occurrences. The two compressor words `u,wu`
do not provide independent labels, as already proved by the centralizer
no-go.

### 2026-08-14: intrinsic transition variance cancels source gauge exactly

`TRUE_TRANSITION_VARIANCE_IS_SOURCE_GAUGE_INVARIANT.md` proves that for
`[C,P]=0`, replacing a compressor `U` by `UC` leaves `UPU*` unchanged and
conjugates every effect `P U*Q_j U P` by `C` inside the source corner. Total
idempotence and commutator energy are therefore exactly invariant. The
single-edge transition route does not require coproduct gauge pinning. Its
remaining theorem is only the fine-fiber refinement: multiplication must
separate target characters which have the same restriction along the proper
coefficient homomorphism. The new matrix identities are transcribed in
`Sofic/TransitionGaugeInvariance.lean`.

### 2026-08-14: one group-like gauge cannot kill packet multiplicity

`FALSE_ONE_COPRODUCT_GAUGE_DOES_NOT_SCALARIZE_THE_MULTIPLICITY.md` gives the
exact countermodel `A=C[lambda(K)] tensor 1`,
`C=rho(g) tensor 1`, `F=1 tensor p` with `rank(p)=1` in `M_4`. The gauge is
perfectly group-like and `F` commutes with all right shifts, yet
`dist_2(F,A)^2=3/16` and a multiplicity unitary has commutator energy `1/2`.
Thus coproduct classification of the compressor gauge and right-shift
synchronization do not close the new dichotomy. The live target must couple
the transported carrier to the gauge coefficient PVM, or directly force the
intrinsic transition-effect variance to vanish.

### 2026-08-14: full-packet gap splits into bounded and multiplicity stages

`TRUE_FULL_PACKET_GAP_SPLITS_INTO_RIGHT_SHIFT_OR_MULTIPLICITY.md` factors the
new `3/16` distance through

```text
C[lambda(K)] tensor 1
 subset C[lambda(K)] tensor M_m.
```

Pythagoras forces at least `3/32-o(1)` into one stage. Reynolds/Haar energy
then yields either a `3/16-o(1)` commutator against one member of a recovered
sixteen-element right-regular packet, or the same energy against one pure
multiplicity unitary. The live compatibility theorem is thereby split into
a fixed finite right-shift assertion and a coefficient-scalarization
assertion; the latter is the only genuinely unbounded part.

### 2026-08-14: the full raw-packet commutant has one fixed-energy witness

`TRUE_FULL_RAW_PACKET_COMMUTANT_WITNESS.md` upgrades the binary-cut symmetry
endpoint using the already certified intersection

```text
K intersect U* K U={1}.
```

For the transported trace-`1/4` carrier `F`, Fourier expectation onto the
entire raw packet algebra is exactly `(1/4)1`.  Hence

```text
dist_2(F,C[K])^2=3/16.
```

Haar averaging over the commutant gives a single coordinate unitary
commuting with all of `K` and having squared commutator at least `3/8-o(1)`
against `F`; a two-by-two dilation makes it a symmetry.  The scalar endpoint
is transcribed in `Leavitt/PauliCarrierBinaryGap.lean`.  The live theorem is
now full-packet bicommutant compatibility: cross-root synchronization must
force `F_n` to commute with every coordinate unitary in
`Alg(rho_n(K))'`.  Separate finite-group exactification does not prove this.

### 2026-08-14: diagonal pairing defects already give spectral invariance

`TRUE_DIAGONAL_PAIRING_DEFECT_SUPPLIES_SPECTRAL_INVARIANCE.md` eliminates the
remaining independent transition hypothesis in the actual contraction-arrow
pairing formulation.  For contractions `W,R,L`, put
`eta=||R* W L-W||_2`.  Mass saturation through the two contractions gives

```text
||W L-R W||_2,
||W* R-L W*||_2 <=eta+sqrt(2 eta),

||[W*W,L]||_2 <=2 eta+2 sqrt(2 eta).
```

Thus the two diagonal decoder defects automatically make `W*W` almost
commute with `L0,L1`.  Choosing the right-factor vertex cover `{L0,L1}` and
applying coarea gives a trace-`>=1/120`, uniformly conditioned common cut for
all three terminal products.  The spectral route has no separate
invariance/synchronization assumption after the three common-coordinate
pairing defects have been extracted.

The exact transition decomposition is transcribed as
`pairing_defect_transition_decomposition`; the scalar mass-loss bound is
transcribed as `contraction_sq_mass_loss_le_two`, and the conditional
propagation theorem is
`hsNormSq_pairing_transition_le_of_range_deficiency`.  The remaining formal
step inside this lemma is the matrix positivity bridge.  The unresolved
research theorem is now common-coordinate extraction of the four
paired-radical contractions with the three diagonal/cross defects.

### 2026-08-14: only the two left Leavitt arrows need spectral invariance

`TRUE_TWO_LEFT_ARROWS_SUFFICE_FOR_SPECTRAL_LEAVITT.md` closes the
post-selection analytic bookkeeping and halves the synchronization family.
For a carrier projection `P`,

```text
P Ri P Sj P-P
 =P(Ri Sj-I)P-P Ri(1-P)SjP.
```

Hence passing the three products `R0S0=I`, `R1S1=I`, `R0S1=0` to the corner
requires leakage control only for `R0,R1`; no invariance of `S0,S1` is
needed.  If `alpha=tau(P)`, `eta` bounds the three ambient product defects,
and `lambda` bounds the two left-arrow leakages, the corner Leavitt theorem
gives

```text
eta+lambda >=sqrt(alpha)(2-sqrt(3)).
```

The coarea cut has `alpha>=1/120`, yielding the fixed ambient floor
`(2-sqrt(3))/sqrt(120)`.  Therefore the spectral fallback now asks for only
two forward/reverse transition pairs, for `R0` and `R1`.  The two exact
compression identities are transcribed in `LeavittTraceFloor.lean`; no local
build was run.

More generally, each product leakage can be charged to either factor, so any
vertex cover of the three edges `(R0,S0)`, `(R1,S1)`, `(R0,S1)` suffices.
The minimum size is two.  The preferred cover is the crossed pair
`{R0,S1}`, precisely the maps whose diagonal injectivity and crossed-zero
relation drive `FinitePairedQuotientObstruction`.  This aligns the spectral
and radical-quotient endpoints around the same two synchronized arrows.

### 2026-08-14: transition intertwinings imply the spectral commutators

`TRUE_TRANSITION_INTERTWINING_CONTROLS_SPECTRAL_LEAKAGE.md` removes the
remaining separately stated commutator hypothesis from the spectral decoder.
For a contraction `T`, source unitary `A`, target unitary `B`, and `H=T* T`,

```text
||[H,A]||_2 <=2||T A-B T||_2.
```

Indeed, with `X=TA` and `Y=BT`, unitary invariance and the Gram factorization
give

```text
||[H,A]||_2=||X*X-Y*Y||_2
 <=||X*(X-Y)||_2+||(X*-Y*)Y||_2.
```

For the Pauli block `T=GF`, spectral coarea now selects one projection of
trace at least `1/120`, with inverse bound `4 sqrt(2)`, satisfying

```text
sum_k ||[P,A_k]||_2^2
 <=64 sum_k ||GF A_k-B_k GF||_2.
```

The new smallest fallback gate is therefore four natural cross-chart
transition-intertwining defects.  Proving those identities from the
multiplication-module packet automatically supplies positive density,
conditioning, one common cut, and two-sided leakage.

The squared matrix estimate is transcribed without placeholders as
`hsNormSq_transitionGram_commutator_le_four` in
`GroupApproximation/Sofic/LeavittTraceFloor.lean`.  It has not been locally
built.

For contraction-valued decoded arrows, the stronger exact identity

```text
[T* T,A]=T*(T A-B T)+(T* B-A T*)T
```

removes the unitary hypothesis.  Its squared estimate is transcribed as
`hsNormSq_transitionGram_commutator_le_two_sided`.  The remaining gate in
that setting is the forward/reverse pair of transition laws; coarea then
bounds the total cut leakage by `32` times the sum of their unsquared
normalized-HS defects.

### 2026-08-14: spectral coarea removes the eigenvalue-gap gate

`TRUE_SPECTRAL_COAREA_INVARIANT_CUT.md` reduces the spectral fallback to a
strictly algebraic commutator estimate.  For `P_t=1_[t,infinity)(H)`, finite
spectral decomposition gives

```text
integral_0^1 ||[P_t,A]||_2^2 dt
 <=||[H,A]||_2 ||A||_2.
```

Summing this for the four coefficient arrows and averaging over
`t in [1/32,1/16]` selects one common coordinate-dependent cut satisfying

```text
tau(P_t)>=1/120,
sum_k ||[P_t,A_k]||_2^2
  <=32 sum_k ||[FGF,A_k]||_2,
```

while the retained singular values are at least `1/sqrt(32)`.  Therefore no
uniform eigenvalue spacing or separately postulated invariant spectral
projection is needed.  The new smallest fallback gate is just

```text
||[FGF,A_k]||_2 -> 0
```

for the four recovered multiplication arrows.  Proving these commutator
estimates from the cross-chart relations would automatically supply one
positive-density, well-conditioned, simultaneously invariant coefficient
sector.

### 2026-08-14: aggregate all negative root characters

`TRUE_NEGATIVE_CHARACTER_SECTOR_AGGREGATION.md` removes a density concern
from the growing Heisenberg/radical-quotient route.  On a finite root window,
each central-character atom has trace `1/|A|`, but the sum of every character
with `ell(1)=1` is exactly the negative cut `(1-u(1))/2` and has trace `1/2`.
If the four quotient contractions are constructed block-diagonally over all
these characters, take their direct sums first and apply the
`2-sqrt(3)` theorem once on the full negative sector.  Unequal block sizes
are absorbed automatically by normalized trace, with no atom selection,
minimum mass, or union bound.  The resulting ambient defect floor is

```text
(2-sqrt(3))/sqrt(2)>0.
```

The missing statement is correspondingly sharper: build the radical-
quotient module operations measurably over the entire negative character
PVM.  The fixed Pauli route remains smaller because it has a fixed four-label
coordinate system, but the growing route no longer needs a positive-mass
single-character theorem.

### 2026-08-14: fixed density removes the decoder's corner-normalization gate

`TRUE_POSITIVE_DENSITY_LEAVITT_DECODER_ENDGAME.md` corrects a small but
important quantifier in the finite-multiplicity decoder.  A merely nonzero
matrix corner is not quantitatively useful: normalized corner error is the
ambient normalized-HS error divided by the square root of the corner trace.
For the existing Pauli packet the initial cut has canonical trace `1/8`.
Consequently the local `2-sqrt(3)` Leavitt floor is already the ambient floor

```text
(2-sqrt(3))/sqrt(8)>0.
```

The missing decoder can therefore be stated without renormalized-corner
estimates: recover the four contractions in the exactified trace-`1/8`
corner and make the three **ambient** product defects tend to zero.  This
also explains why the fixed Pauli packet should be attempted before a
growing Heisenberg-character sector: a vanishing sector would require the
extra rate `error=o(sqrt(corner trace))` or a positive-mass selection
theorem.  The terminal contradiction and its constants were already
formalized; common-coordinate coefficient extraction remains the only new
mathematical gate.

### 2026-08-14: a phase-safe toric gap would be enough

`TRUE_NORMAL_TORIC_GAP_IMPLIES_NONHYPERLINEAR.md` proves a broader exact
game-to-group reduction.  For a finite two-player torically determined game,
adjoin its finite scalar phase group `B` to the universal game group and
quotient by the normal closure `N` of the clauses.  If

```text
N intersect B={1}
```

and `omega_qa<1`, then this finitely presented quotient is nonhyperlinear.
Indeed a hypothetical hyperlinear embedding has a positive central character
corner for `B`; the normalized corner trace satisfies every clause exactly,
and matrix microstates plus left/right multiplication give strategies with
value tending to one.  No approximate-representation stability theorem is
needed.  Normality of the clause subgroup is a sufficient special case, so
full LCS syntax is stronger than logically necessary.

The exact Watts--Helton--Klep criterion only gives scalar nonmembership in the
clause subgroup, not in its normal closure; an explicit `C_2 times A_5`
example shows normal closure can kill the phase.  Moreover any toric
`omega_qc=1>omega_qa` gap must have an infinite clause subgroup whose
projection to the universal game group has infinite index: finite clauses
are separated in a finite quotient of the residually finite universal group,
and finite-index clauses give a finite-dimensional induced strategy.  The
new live compiler target is therefore a toric gap with phase-safe normal
closure, not necessarily an LCS game.

Phase safety has a useful trace certificate.  If the clauses are satisfied
in `L2` by a tracial representation of the *full* toric universal group, its
trace kernel is normal and contains the normal closure; the faithful scalar
character then forces `N intersect B={1}`.  Hence a tracial toric `qc/qa` gap
already gives the nonhyperlinear quotient.  Synchrony alone is insufficient:
the standard synchronous trace lives on a one-player/opposite-algebra model,
and the full two-player toric words need not descend without order reversal.

The direct BCS answer-algebra compiler is now closed exactly.  For one
constraint with satisfying set `R<={+1,-1}^k`, its coordinate consistency
observables can all be scalar group monomials in a finite abelian answer
group algebra iff `R` is affine.  On the group spectrum the coordinates are
characters, so their joint image is affine; conversely an affine `R` is
realized by its translation space.  Finite answer duplication has the same
joint-image obstruction.  Thus the standard constraint--variable BCS format
is locally toric precisely in the LCS case.  Any broader phase-safe toric
compiler must use a genuinely nonlocal/nonabelian multi-question gadget.

There is an exact corner-level escape.  For any Boolean predicate
`R subseteq {+1,-1}^k`, the sum `p_R` of its allowed Fourier atoms in
`C[(C_2)^k]` has canonical trace `|R|/2^k`, and

```text
p_R C[(C_2)^k] p_R = C^R.
```

Thus arbitrary predicates, including nonaffine ones, are exact local finite
group-algebra corners.  The global obstruction is now one reducing
projection: local context projections need not commute, their product is not
a projection, and a projection commuting with all variable generators is
central in the bare context group factor.

The first alternative target, an algebraic subgroup-average Hecke corner
`p_K C[Gamma] p_K`, is now ruled out exactly.  Group-ring augmentation maps
`p_K` to `1`, so every such corner has a unital character; any BCS operators
inside it would therefore give a classical satisfying assignment.  The
corrected target is an augmentation-zero signed Hecke corner
`z_rho L(Gamma) z_rho`, where `rho` is a higher-dimensional irreducible type
of a finite subgroup.  Its block projection has positive canonical trace and
is killed by every scalar group character.  Every Boolean predicate still
has an exact character-free local model: for `r` allowed assignments, place
the coordinate signs diagonally on `C^R` and adjoin every permutation of the
assignment basis.  The resulting finite signed-permutation group acts
irreducibly, and every coordinate sign is an actual group element in its
selected `M_r` block.  The sole remaining gate is therefore global
trace-preserving selection and gluing of these nontrivial finite types.  See
`TRUE_AUGMENTATION_ZERO_HECKE_GATE.md` and
`TRUE_BCS_PREDICATES_ARE_LOCAL_FINITE_GROUP_CORNERS.md`.

The full irreducible type cannot be simplified to the existing central
Clifford sign.  If a finite central character selects a unique irreducible
block and `D` is any abelian subgroup containing that center, induction of
each character of `D` extending the central phase lies entirely in the
selected sector; Frobenius reciprocity forces every such character to occur
in the unique block.  Hence an extraspecial negative spin packet, including
the fixed eight-lamp `M_16`, cannot locally prune a nonlinear Boolean
predicate.  It can still carry coefficient holonomy, but the selector must
remember the full nonabelian irreducible type.

The global operator form has also been reduced.  For any projection `q` and
group unitary `g`, the compression `qgq` is unitary in `qMq` iff `g` commutes
with `q`.  Hence a compiler in which every BCS variable is one compressed
group element lies entirely in the stabilizer of the selector.  For a
finite-support selector this is a finite-normal representation sector, and
Clifford theory reduces it to a fixed matrix block over a twisted quotient
group algebra--the existing projective/central-extension gate.  A genuinely
nonnormal Hecke compiler must instead make at least one variable a linear
combination of multiple double cosets whose cross terms cancel exactly.

The signed-corner endpoint does **not** require a trace-preserving embedding
of a preselected non-CE trace.  Choose a finitely presented BCS algebra which
has tracial states but no CE tracial state at all.  Any unital homomorphism
from it into `q C[Gamma] q` pulls the normalized canonical corner trace back
to a tracial state.  If `Gamma` were hyperlinear, the corner and the GNS
algebra of that pulled-back trace would be CE, an immediate contradiction.
Thus the remaining signed-Hecke target is purely algebraic: construct one
positive augmentation-zero corner and self-adjoint involutions satisfying
the finite BCS relations.  Injectivity, prescribed moment matching, and a
trace decoder have all disappeared.

`TRUE_PIECEWISE_SIGNED_HECKE_COMPILER.md` supplies an exact constructive
normal form for the required multi-double-coset involutions.  If
`q=sum p_i=sum r_i` are two algebraic projection partitions and group words
`g_i` carry `p_i` to `r_i`, then `sum g_i p_i` is a corner unitary; pairing
the arrows with their inverses makes it self-adjoint.  With two pieces,
`q=p_0+p_1` and `g p_0 g^(-1)=p_1` already give the nonnormal involution
`g p_0+g^(-1)p_1`.  A whole BCS representation is equivalently a finite
projection atlas: one allowed-atom partition per context, with equality of
the signed coordinate sums on every overlap.  This is now the smallest
purely algebraic groupification gate.

Ordinary Bass--Serre gluing of these local gadgets is ruled out: the
fundamental group of a finite graph of finite groups is virtually free and
hence hyperlinear, so all of its positive finite-subgroup Hecke corners are
CE.  Any successful corner compiler must introduce genuinely
higher-dimensional compatibility/holonomy or an infinite coefficient group;
a tree of finite predicate gadgets cannot carry the non-CE trace.

The firewall extends to infinite pieces: hyperlinear groups are closed under
amalgamated free products and HNN extensions over amenable subgroups.  Hence
a finite graph of hyperlinear vertex groups with amenable edges is still
hyperlinear.  Merely replacing a finite predicate vertex by an infinite
hyperlinear gadget cannot work; the escape must be higher-dimensional or
must introduce nonamenable gluing with genuinely new trace control.

### 2026-08-14: regular tensoring cannot groupify a non-CE game trace

`FALSE_GAME_REPRESENTATION_REGULARIZATION_BY_FELL_ABSORPTION.md` closes the
most direct canonical-trace shortcut from a perfect game to a group factor.
For every representation `pi:G->U(K)`, the diagonal representation

```text
g |-> pi(g) tensor lambda_G(g)
```

has the regular character, but the fiberwise Fell unitary
`W(xi tensor delta_h)=pi(h^(-1))xi tensor delta_h` conjugates it to
`1 tensor lambda_G`.  Hence its generated von Neumann algebra is spatially
just `L(G)`; the possibly non-CE game representation has been absorbed, not
implanted.  A genuine Hecke-corner route would have to place the game algebra
normally and trace-preservingly inside a canonical group-factor corner, which
is essentially the still-open groupification theorem itself.  This leaves
the one-instance perfect BCS-to-LCS compiler as the direct game lane.

### 2026-08-14: the full Fourier space already has a quantum unitary gap

The constant kernel produced by the crossed-zero pairing relation should not
be deleted.  In `M_N(C)` with normalized trace, put
`K_N=N^(-1/2)J_N tensor 1`.  For every operator-norm contraction `T`,
compression to the constant-label projection gives

```text
||T-K_N||_2^2 >= (1-1/sqrt(N))^2 >= 3/2-sqrt(2)   (N>=2).
```

This is operator-valued and requires neither unitarity of `T`, commuting
coefficients, nor a classical permutation.  Hence, if the atlas produces
one common finite Fourier packet with contracted transports `R_n,L_n` and
`||R_n*F_(b,n)L_n-K_(N_n)||_2->0`, the hyperlinear contradiction is
immediate.  The final analytic step no longer needs whole-map PVMs,
multiplication-table classicalization, the two diagonal identities,
trivial-mode deletion, polar repair, or the `2-sqrt(3)` contraction gap.  The
remaining gate is specifically to recover a positive-trace common
coefficient packet with a flat pairing Fourier operator and complete
cross-operator control.  Leakage only matters through the error in that
complete identity.  Local Pauli signs and separate block-mass marginals do
not supply the packet.  A common multiplicity holonomy `C` is harmless,
because right multiplication reduces
`N^(-1/2)J_N tensor C` to the scalar kernel.  On the already forced
two-qubit Pauli packet `N=4`, the contraction gap is exactly `1/4`; a
growing radical quotient is unnecessary if one can align the sixteen
crossed blocks to one coefficient operator.  See
`TRUE_FULL_SPACE_QUANTUM_FOURIER_GAP.md`.

The exact trace-flat masses close the amplitude part of that fixed-packet
endpoint.  In the normalized trace-half carrier, every one of the sixteen
operator blocks has coefficient `L2` mass squared `1/8`.  If phase-corrected
row/column covariance makes them asymptotically equal to `C_n/2`, then
`||C_n||_2->1/sqrt(2)`.  But a constant-block contraction satisfies

```text
||T-(J_4/2) tensor C_n||_2 >= ||C_n||_2-1/2,
```

leaving the fixed squared gap `3/4-1/sqrt(2)`.  The sole analytic gate is
therefore a sixteen-block coherence estimate.  It can be phrased as
Reynolds invariance under the fixed group `C_2^2 times C_2^2`, requiring only
four translation defects and no growing-outcome rounding.  The translations
cannot be literal group words: that would force the same contradiction in
the regular representation, as in
`FALSE_LITERAL_FIBER_MIXER_SHORTCUT.md`.  They must be coordinate-dependent
shifts recovered from equal-rank finite matrix blocks, with the
multiplication-module relations controlling their four defects.  See
`TRUE_TRACE_FLAT_COMMON_BLOCK_CONTRACTION_GAP.md`.

### 2026-08-14: two coproduct defects suffice for classicalization

`TRUE_APPROXIMATE_BICOREPRESENTATION_CLASSICALIZATION.md` removes the exact
`beta,gamma` hypothesis from the uniform multiplicative-unitary endpoint.
For any unitary `V in Ahat tensor C tensor A`, let `delta_L,delta_R` be its
two primal/dual coproduct defects. Comparing the two five-leg expansions and
cancelling their common outer unitaries gives

```text
||V_234 V_135-V_135 V_234||_2
  <=3(delta_L+delta_R).
```

Parseval converts this to normalized mean coefficient-commutator energy at
most `9(delta_L+delta_R)^2`, uniformly in the finite quotient size. Thus no
growing-presentation stability modulus is needed. The live atlas statement
is now one direct estimate: construct the relative transport `V_n` after
additive packet exactification and control both complete coproduct defects by
the fixed cross-root relator defect. The terminal metric inequality is
formalized source-first; no build was run.

### 2026-08-14: the multiplication classicalizer is size-uniform

`TRUE_UNIFORM_MULTIPLICATIVE_UNITARY_CLASSICALIZATION.md` quantifies the
Kasprzak--Sołtan--Woronowicz five-leg proof. For exact primal and dual finite
Kac-table star-homomorphisms `beta,gamma`, let

```text
V=(id tensor beta)W,   V'=(gamma tensor id)W.
```

If `||V-V'||_2=epsilon`, the two five-leg expansions are within
`3 epsilon` and `6 epsilon` of the same operator. Cancelling their common
outer unitaries gives

```text
||V_234 V_135-V_135 V_234||_2<=9 epsilon.
```

Parseval turns its square into normalized average coefficient-commutator
energy, bounded by `81 epsilon^2` with no dependence on matrix dimension or
finite-table size. This crosses the growing-quotient stability boundary at
the correct total-error scale. The live interface is now construction of
the two exact coordinate table homomorphisms and control of their single
Fourier compatibility defect by the fixed cross-root relators. The terminal
`3+6=9` bi-invariant metric argument is formalized source-first; no build was
run.

### 2026-08-14: full multiplication coherence forces classical maps

`TRUE_MULTIPLICATION_TABLE_QUANTUM_CLASSICALIZATION.md` identifies a
strictly stronger replacement for the false Hadamard-classicality shortcut.
Kasprzak--Sołtan--Woronowicz prove that quantum automorphisms of finite
quantum groups are classical. For a finite ordinary group `Q`, a magic
transport matrix satisfying the full Hopf/multiplication table therefore has
commuting coefficients. Their products give an explicit PVM indexed by
`Aut(Q)`, so the entire response map is one classical latent outcome rather
than a collection of unrelated label marginals.

This plugs directly into the existing edgewise whole-map PVM and tree-gluing
endpoint. The remaining atlas theorem is now operator-native: recover a
magic transition matrix satisfying the full finite multiplication table from
the cross-root relations. For fixed `Q`, tracial-ultraproduct compactness
already gives asymptotic coefficient commutation. For growing `Q_n`, one
must either exactify the table coordinatewise or prove a size-uniform
multiplicative-unitary estimate. The primary theorem supplies exact
classicalization, not that still-missing uniform extraction.

### 2026-08-14: a literal extension-fiber mixer is impossible

`FALSE_LITERAL_FIBER_MIXER_SHORTCUT.md` closes the attempted synthesis of the
binary conditional-variance endpoint with a fixed word library. If a group
action is transitive inside every extension fiber and a binary label is
invariant under that action, the label is already constant on each fiber.
Equivalently, Reynolds averaging on the diagonal atom algebra is the coarse
fiber conditional expectation, and its mean commutator energy is twice the
conditional variance.

If fixed literal atlas words supplied both the fiber action and label
invariance, the same exact identities would hold in the regular
representation and would make the canonical transported carrier measurable
in the parent binary algebra. This contradicts its exact squared residual
`3/16`. Thus another literal word search cannot manufacture the missing
mixer. The live route is necessarily matrix-specific: recover a
coordinate-dependent multiplicity action or whole-map PVM, then apply the
Reynolds/majority identities. The finite-set implication is formalized
source-first as `invariant_label_eq_of_same_fiber`; no build was run.

### 2026-08-14: finite normal generation does not give a uniform atlas repair

`FALSE_ATLAS_KERNEL_BOUNDED_NORMAL_WIDTH.md` closes the shortcut that tried
to propagate the finite atlas-relator defect to every dimension-dependent
coefficient word with one uniform telescoping constant.  The source
`P=A8*A8` is non-elementary virtually free and its nontrivial kernel
`N=[P,R]` acts non-elementarily on the Bass--Serre tree.  A homogeneous
Bestvina--Fujiwara quasimorphism is nonzero on `N`.  Since such a
quasimorphism is conjugation invariant and grows linearly on powers, the
number of conjugates of any fixed finite normal-generating set required to
express elements of `N` is unbounded.

The quotient's normal-width-two survivor theorem is therefore irrelevant to
kernel area.  The paired-radical extraction cannot request relations whose
word decompositions depend on the coordinate dimension and then appeal only
to finite normal generation.  A successful proof must control the carrier
by a fixed analytic cross-root estimate, without paying dimension-dependent
normal area.  The quantitative quasimorphism/product bound is formalized
source-first in `Monsters/TwoConjugacyClasses.lean`; no build was run.

### 2026-08-14: `(TT)/T` does not cross the growing-dimension HS gate

`FALSE_TT_T_IS_NOT_DIMENSION_FREE_HS_STABILITY.md` audits the strongest
available Ulam-stability shortcut.  The existing atlas theorem is property
`(TT)/T`, not property `(TTT)`.  More importantly, even the Burger--Ozawa--
Thom `(TTT)` conclusion concerns operator-norm almost representations and
fixes the matrix dimension before taking the defect to zero.  Hyperlinear
witnesses provide only normalized-HS defects in dimensions `d_n -> infinity`;
converting to operator norm costs `sqrt(d_n)`, and the stability modulus may
also depend on `d_n`.  Thus the theorem does not yield a dimension-free or
flexible normalized-HS rounding theorem.  Becker--Lubotzky's instability
theorem for infinite hyperlinear property-`(T)` groups is the consistency
check against any generic upgrade.

The valid target is a uniform estimate for this explicit atlas relator
packet, not abstract quasi-cocycle rigidity.  Such an estimate is equivalent
in strength to the surviving finite-multiplicity multiplication/leakage
gate; it has not been proved here.

### 2026-08-14: the star synchronizer cannot orient leakage

`FALSE_STAR_SYNCHRONIZATION_DOES_NOT_CREATE_LEAKAGE.md` closes the combined
shortcut "spatialize Leavitt star, then obtain a one-way coefficient cut."
For doubled matrices `W=diag(W0,W1)` and `P=diag(P0,P1)`, both forward and
reverse leakage are diagonal and their squared normalized-HS masses are the
averages of the corresponding sheet masses.  One-cut balance holds on each
unitary sheet, hence also after doubling.  The sheet swap commutes with the
raw cut `diag(e,e)` because the involutive automorphism fixes the raw
involution.

The exact block and mass identities are formalized source-first in
`Sofic/InvolutiveTwoSheet.lean`; no local build was run.  Star
synchronization remains useful only for identifying opposite-root blocks as
adjoints.  The live theorem must still use a cross-root multiplication word
to restrict multiplicity holonomy and create support containment or
asymmetric leakage.

### 2026-08-14: positive-rank carriers do not inherit the Leavitt gap

`FALSE_WEIGHTED_LEAVITT_CONTRACTION_GAP.md` closes the shortcut that tried to
combine the `1/120` trace-flat spectral sector directly with the full-space
contraction obstruction.  There is an exact `2 x 2` countermodel on the
rank-one carrier `P`: with `S0=T0=P`, `S1=E21`, and `T1=E12`, all four maps
are contractions and

```text
T0 S0 P=P,    T1 S1 P=P,    T0 S1 P=0.
```

The forward arrow exits `P` and the reverse arrow returns it.  Thus neither
positive density nor a singular-value floor prevents perfect compressed
Leavitt relations.  The exact products are formalized source-first as
`properCarrier_exact_weighted_leavitt_relations` in
`Sofic/LeavittTraceFloor.lean`; no local build was run.

The live spectral endpoint is consequently exact: prove that the selected
sector has a common positive-density reducing subprojection for the four
actual multiplication arrows, or turn its leakage into a fixed imbalance.
No weighted trace-only argument can replace this invariance/leakage theorem.

### 2026-08-14: normal full-group characters force residual finiteness

`FALSE_NORMAL_FIXED_POINT_CHARACTER_GROUPIFICATION.md` closes the entire
normal-character repair of the Manzoor/full-group bridge. Fourier
coefficients of a normal state on `L(Lambda)` vanish at infinity. Since the
fixed-point character is conjugation invariant, only FC elements can have
positive-measure fixed sets. Their finite conjugacy orbits generate an
increasing family of finite-dimensional invariant Cartan algebras;
W*-generation forces this family to be dense. The full-group action is
therefore profinite and faithful, so its finite atom actions separate
`Lambda` and make it residually finite. A normal W*-generating
representation would then make the relation factor a central summand of the
CE algebra `L(Lambda)`, impossible for a non-CE relation factor.

The algebraic endpoint is now formalized source-first as
`residuallyFinite_of_separating_finite_actions`: any point-separating family
of finite atom actions gives residual finiteness. The analytic normal-state
and Cartan-expectation portions remain paper proofs; no build was run.

Thus infinite stabilizers do not rescue the canonical construction by
upgrading weak containment to a normal group-factor representation. Any
Manzoor conversion must be noncanonical at the operator level.

### 2026-08-14: fixed adjoint-expander binder for the Pauli carrier

`TRUE_FIXED_LIBRARY_EXPANDER_BINDER.md` replaces the moving Haar-selected
symmetry by an exact finite-library criterion. If fixed words `V_1,...,V_k`
commuting with the parent cut have adjoint average `T` and the centered
carrier `X` satisfies

```text
Re <X,(1-T)X> >= kappa ||X||_2^2,
```

then the Pauli multiplicity floor gives average squared commutator energy at
least `kappa/4`; hence one fixed word witnesses that floor. The remaining
coordinate theorem is now carrier-specific: show that this one `X_n` has a
uniformly positive component off the invariant algebra of one fixed finite
word library. Property (T) alone does not identify that invariant algebra.
The scalar `kappa/4` endpoint is formalized in
`Leavitt/PauliCarrierBinaryGap.lean` without running a build.

### 2026-08-14: finite stabilizers cannot groupify a diffuse relation algebra

`FALSE_FINITE_STABILIZER_FULL_GROUP_GROUPIFICATION.md` closes the finite
isotropy version of the Manzoor/full-group bridge. For an ergodic action, the
stabilizer IRS is ergodic. If it is supported on finite subgroups, countability
of the finite-subgroup space forces it to be supported on one finite
conjugacy orbit. Hence every fixed-set indicator belongs to a single
finite-dimensional subalgebra `B` of the Cartan. The canonical Cartan
expectation maps the entire subgroup von Neumann algebra into `B`, so those
unitaries cannot generate a diffuse relation algebra.

The only stabilizer version left uses infinite stabilizers. Amenability gives
quasi-regular weak containment in the group regular representation, but only
at the reduced-C-star level; it does not give normal containment of the GNS
factor in the group factor. That upgrade is again the regular-to-natural
trace-selection problem. Thus finite isotropy is now ruled out rather than
left as a possible compromise between essential freeness and Cartan recovery.

### 2026-08-14: projective unitary groups reduce cardinality, not trace selection

The shortcut through a separable non-Connes-embeddable factor `M` has now been
audited in `FALSE_PROJECTIVE_UNITARY_GROUP_SHORTCUT.md`. There is one useful
exact reduction: if the abstract discrete group `PU(M)` were nonhyperlinear,
locality would produce a finitely generated nonhyperlinear subgroup. The new
formal theorem `exists_not_isHyperlinear_iff_exists_fg` records that existence
of a nonhyperlinear group is equivalent to existence of a finitely generated
one, without any soficity assumption.

The hoped-for premise does not follow from known unitary rigidity. A tracial
matrix ultraproduct is generally nonseparable, hence outside Dowerk--Thom's
Polish-SIN automatic-continuity theorem. Restriction to a countable dense
subgroup loses the theorem's domain hypothesis. Dye reconstruction needs an
orthoisomorphism or a sufficiently strong full-unitary-group isomorphism, not a
raw monomorphism into a larger unitary group. Most decisively, hyperlinearity
approximates the regular character `delta_e`, whereas the representation that
recovers `M` uses the natural character `tau_M`. The missing result is again a
trace-selection theorem, now in a very clean form.

The quotient boundary is now also formalized exactly. Every group is a
quotient of a hyperlinear free group, so arbitrary quotient permanence for
hyperlinearity is equivalent to universal hyperlinearity itself. Dually, a
nonhyperlinear group exists exactly when a hyperlinear free group has a
nonhyperlinear quotient. This prevents the non-CE natural representation of
`PU(M)` from being silently treated as a quotient-closure argument.

### 2026-08-14: the ambient Bernoulli group does not Haar-groupify the non-CE IRS

`FALSE_MANZOOR_IRS_AMBIENT_HAAR_GROUPIFICATION.md` closes a hidden version of
the algebraic-Haar shortcut. Although `Sub(F)` is a conjugation-invariant
subset of the compact binary group `{0,1}^F`, it has product-Haar measure
zero. The natural Haar family that is supported on subgroups—kernels of
random binary characters—has trace `(1/2)1+(1/2)1_N` with
`N=[F,F]F^2`, hence an amenable GNS representation generated by the trivial
and regular representations of the elementary abelian quotient `F/N`.

The exact positive target is now a non-CE p.m.p. action with a countable
multiplicative orthonormal basis permuted by the acting group. Such a basis
is equivalent to an algebraic compact-abelian Haar model and turns the
crossed product into a discrete semidirect-product group factor. Manzoor's
weak-star pseudo-subgroup compactness construction supplies no such basis;
for its free acting group, amenable-extension permanence proves that none can
exist.

### 2026-08-14: one symmetry witnesses the Pauli multiplicity floor

`TRUE_PAULI_MULTIPLICITY_HAS_ONE_SYMMETRY_WITNESS.md` sharpens the current
nonhyperlinear endpoint. In every finite coordinate, balanced-symmetry Haar
averaging turns the fixed multiplicity variance `1/8+2y` into one
self-adjoint involution `V` with `[V,E]=0` and

```text
||[V,Phi_E(F)]||_2^2 >= 1/4+4y >= 1/4.
```

The full coefficient algebra therefore need not be reconstructed at the
terminal step. The live theorem is a single-symmetry relative-bicommutant
statement binding every coordinate `E`-commuting involution to the
cross-root multiplication module. The involution is coordinate-dependent,
so this is not yet a fixed group word or a proof of nonhyperlinearity.
Another finite Pauli commutator does not address the gate.

### 2026-08-14: exact no-signaling boxes close the label-law shortcut

`FALSE_NONSIGNALING_PAIRED_QUOTIENT_SHORTCUT.md` gives an elementary exact
countermodel to the idea that compatible labelwise pair laws might suffice.
For every perfect binary pairing of size `N>=4`, the uniform law on nonzero
pairs of prescribed pairing value has uniform nonzero marginals.  Using the
prescribed value on the two diagonal contexts and value zero on the crossed
context wins all three constraints exactly with common no-signaling
marginals.  These laws depend jointly on each source pair and therefore do
not come from whole response maps.

The corresponding Fourier sign table is Walsh--Hadamard.  Generic Hadamard
rigidity cannot classicalize it: every Hadamard matrix of size at least four
has nonclassical quantum symmetries.  See
`FALSE_HADAMARD_QUANTUM_SYMMETRY_CLASSICALIZATION.md`.  Rank one is not a
replacement because the coefficient arrows need not preserve a selected
line.  The live theorem is unchanged but now strictly delimited: synchronize
the raw branch decoder with every source in each comb extension fiber by
using the special cross-root multiplication relations.

`TRUE_BINARY_EXTENSION_FIBER_MAJORITY_DECODER.md` converts that live
synchronization statement into one quantitative operator estimate.  If `B`
is the binary raw-branch projection and `A_Y` is the coarse algebra generated
by source-character fibers, fiberwise majority decoding has total error at
most

```text
2 ||B-E_{A_Y}(B)||_2^2.
```

The scalar factor-two comparison is formalized source-first in
`FiniteBinaryFiberDecoder.lean`.  The next relation search should therefore
target asymptotic `L^2` membership of each named binary branch statistic in
`A_Y`, rather than construct a decoder or whole-map PVM directly.  The
finite-window sum of these binary errors and multiplication compatibility
remain part of the gate; one branch bit alone is not the whole response map.

On the existing Pauli-carrier route this becomes an even shorter terminal
statement.  If `E` is the trace-`1/8` parent cut and `F=U*QU` the
trace-`1/4` transported carrier, then every `F` has squared distance at least
`3/28` from the binary algebra `W*(E)`.  Therefore it is enough to prove
`dist_2(F,W*(E))->0`; the former directed containment `F<=E` is unnecessary.
See `TRUE_PAULI_CARRIER_BINARY_ALGEBRA_GAP.md` and the source-first scalar
certificate `PauliCarrierBinaryGap.lean`.

The existing exact intersection certificate makes this endpoint scalar.
The parent order-16 cell containing `E` intersects its comb conjugate
containing `F` only in the identity, so the canonical trace gives
`tau(EF)=1/32`.  Consequently `E_(W*(E))(F)=(1/4)1` and

```text
||F-(1/4)1||_2^2=3/16.
```

More precisely, for every `a,b` the actual packet satisfies

```text
||F-(aE+b(1-E))||_2^2
 =3/16+(1/8)(a-1/4)^2+(7/8)(b-1/4)^2.
```

The shortest remaining Pauli hypothesis is therefore still binary-algebra
membership `dist_2(F,W*(E))->0`.  The canonical mixed moment then identifies
the unique best coefficients as `1/4,1/4`, so scalar collapse is a consequence
of the gate rather than a stronger premise silently substituted for it.  The
completed-square identity is recorded source-first in
`PauliCarrierBinaryGap.lean`.

The gap has an exact two-stage decomposition.  With
`y=tau(EFEF)=||EFE||_2^2>=0`, its Pauli off-diagonal part is `1/16-2y`, while
the sum of the two centered diagonal-block variances is `1/8+2y`.  The latter
is therefore at least `1/8` by itself.  See
`TRUE_PAULI_BINARY_GAP_IS_MULTIPLICITY_VARIANCE.md`.  This closes the idea
that one more finite Pauli commutator might suffice: parity rounding leaves a
fixed multiplicity-variance obstruction.  The live cross-root estimate must
act on the multiplicity coefficients and scalarize both parent sheets.

### 2026-08-13: perfect paired labels have a universal `1/36` error floor

`TRUE_ROBUST_PAIRED_QUOTIENT_HAMMING_FLOOR.md` removes the Fourier and
near-bijectivity subgates from the paired-radical endpoint.  For a nonzero
finite perfect binary pairing, two approximate diagonal transports and one
crossed-zero transport satisfy

```text
eps01 + 4 eps00 + 4 eps11 >= (N-1)/(2N),
max(eps01,eps00,eps11) >= 1/36.
```

The diagonal relations themselves force the two relevant label maps within
`4 eps` of permutations.  The same inequality averages over a common law on
permutation quadruples.  Four arbitrary doubly stochastic block-mass
marginals are not enough: the two-label error is governed by a joint
four-index coupling, and multiplying the marginals assumes the missing
independence.  The remaining analytic theorem must extract finite
perfect-pairing labels and a common classical latent-map lift of the
three observed couplings from normalized-HS coordinates.  See
`FALSE_INDEPENDENT_BISTOCHASTIC_KERNEL_EXTRACTION.md`.

The cross-context compatibility part is elementary once pair-laws on whole
maps exist: the context graph is the tree `L0--R0--L1--R1`, so matching the
shared marginals gives a global law by finite conditional-product gluing.
See `TRUE_TREE_GLUE_COMMON_TRANSPORT_LAWS.md`.  The live matrix theorem is
pairwise classicalization at whole-map level, not four-way synchronization.

`TRUE_EDGE_PVM_LOCALITY_CRITERION.md` gives the smallest exact operator
premise for this step: four PVMs indexed by whole response maps, commuting
only on the three context edges.  Their trace products are compatible edge
laws and tree gluing applies.  The atlas currently supplies finite Pauli
label PVMs but not whole-map PVMs; this is the precise locality gap.

The independent-kernel endpoint is nevertheless exact and stronger: after
averaging source labels, independently sampled bistochastic targets are
uniform, so their crossed one-density is exactly `(N-1)/(2N)`.  This is
formalized by `independentKernelOneMass_perfect`.  Fourier-flatness,
trivial-mode removal, and singular-value invariance are no longer separate
obligations once the required common classical lift is available.

The existing four raw coefficient cuts are not those labels: their comb
kernel is exactly uniform after carrier conditioning.  The required kernels
must be extracted from the deeper multiplication/radical quotient.

`TRUE_CHARACTER_PVM_COARSENING_TO_MAP_OUTCOMES.md` removes a misleading
large-outcome subgate.  Once one finite additive character PVM has a
multiplication-coherent decoder, its atoms coarsen canonically to the required
whole-map PVM; positivity, normalization, edge commutation, and shared
marginals are preserved.  The unresolved theorem is therefore precisely
construction of that decoder from cross-root multiplication, not rounding
`|V|^|V|` unrelated projections.

The radical quotient rank may also vary across character atoms.  Since the
pointwise weighted error floor is at least `1/4` for every nonzero binary
fiber, averaging over a bundle of different ranks preserves the same floor.
No positive-trace fixed-rank selection lemma is needed; the decoder may be
fibered by character and rank.

`TRUE_RAW_SWAP_FULL_BRANCH_ROUTING.md` identifies the decoder already present
in the local group packet.  The raw word fixes the `0` branch, moves the `1`
branch to the last coordinate, and preserves the complete
`t_l s_k=delta_lk` commutator table.  The only missing decoder datum is now
global: make this branch label a deterministic function on the comb
compressor's many-to-one extension fibers.  No further local Pauli or
cross-zero relation is required.

### 2026-08-13: finite paired-radical endpoint is closed

The exact finite contradiction behind the paired-radical program is now
kernel-checked in
`GroupApproximation/Leavitt/FinitePairedQuotientObstruction.lean`.  Two
diagonal pairing-preserving transports force the relevant left and right
maps to be bijective on finite separating quotients; the crossed-zero
transport then annihilates the whole pairing.  See
`TRUE_FINITE_PAIRED_QUOTIENT_OBSTRUCTION.md`.

This does not close hyperlinearity.  The sole live step is analytic: extract
the two finite separating quotients and those three transport identities,
with a flat/reduced Fourier pairing and dimension-independent normalized-HS
loss, from one common atlas microstate.

### 2026-08-13: an all-depth germ quotient closes the hard-only branch

`FALSE_HARD_PACKET_EVENTUAL_ZERO_GERM.md` upgrades the bounded hard-pair
search to a structural theorem.  All six hard pairs and their stars preserve
the same three eventually-zero rays.  The resulting `M_3(F_2)` star
representation sends each recovered parent and its `0` child to the same
rank-one idempotent and kills the `1` child.  Hence no word at any depth in
the combined hard-pair algebra can implement the complementary equivalence.
The zero-range algebraic endpoint is Lean-checked in
`Leavitt/ZeroRangeObstruction.lean`.

The full raw and comb elements act identically on this quotient, but their
source factorizations do not: four of six raw syllables and eleven of 28 comb
syllables leave the germ sector before returning.  The properly infinite
packet is not refuted, because its parent `p_11` is killed by the quotient.
The live theorem remains recovery of `p_11,p_001` and the completed
compressor corners in one finite multiplicity algebra.  Intermediate
source-prefix holonomy is a possible tool for that recovery, not a premise
silently inserted into the endpoint.

### 2026-08-13: hard two-branch search extended without a complementary child

`FALSE_HARD_PAIR_TWO_CHILD_SHORT_PACKET.md` now records an exact all-pair
search through mixed-word depth seven (`60,240` reduced Leavitt values) and a
targeted search of the smallest-growth hard representative through depth
nine (`39,364` values).  Every recovered base-to-child matrix unit still
ends in the `0` child; no complementary `1`-child equivalence appears.  The
search CLI now requires explicit depth, target bits, and pair scope so deeper
bounded audits do not silently reuse the archived depth-six parameters.

The bounded scan itself is not an all-depth theorem, and a depth-ten run was
deliberately killed by the 50-second MSI bound.  The preceding germ-quotient
entry now supplies the structural all-depth closure.  Brute-force hard-pair
word growth is retired; only the separate finite-multiplicity recovery of the
known raw/comb properly infinite packet remains live.

### 2026-08-13: the classical `SL_3(Z)` shortcut closes only the non-MF paper gate

`SL3_PRESENTATION_PROPERTY_T_AUDIT_2026-08-13.md` verifies that the literal
rotation presentation is the matrix-labelled CRW presentation of
`SL_3(Z)`.  Classical property `(T)` and the checked intrinsic affine bridge
therefore discharge the property-(T) hypothesis in the paper proof of the
literal non-MF example.  The staged `P13` Hodge certificate is unnecessary
for that human argument but now supplies the kernel proof: Lean checks its
exact rational residual blocks and transports the result through the literal
quotient and affine bridge without importing a published theorem as an axiom.

This does not advance the same marked word toward nonhyperlinearity.  The
finite coset-tower model in `TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md` sends
that word to `-1` in a Connes-embeddable representation, and Becker--Lubotzky
show that infinite hyperlinear property-(T) groups such as `SL_3(Z)` are not
stable in normalized Hilbert--Schmidt metric.  Thus classical property `(T)`
cannot supply the missing flexible-HS stability input in
`TRUE_CLIFFORD_HYPERLINEARITY_FORCES_AMBIENT_HS_INSTABILITY.md`.  The live
hyperlinear gate remains coefficient/multiplicity recovery, not the base
property-(T) certificate.

### Retired eight-lamp spin note: keep only the future gate

The former root manuscript `nonhyperlinear_spin_reduction.tex` has been
removed from the main project because it was a reduction and stopping theorem,
not an unconditional nonhyperlinear endpoint.  Two proved lessons remain
useful for future work:

- in a hypothetical trace-preserving model with the central mark equal to
  `-1`, the eight affine-coset lamps generate the canonical spin factor
  `Cl_8(C) ≅ M_16(C)`, leaving an inverse-projective coefficient action;
- regular tensor amplification preserves that spin packet while forcing the
  ordinary normalized low-spectral adjoint rank to vanish, so a
  positive-density argument from the fixed `M_16` factor cannot close the
  problem.

The viable future gate is therefore a relative or center-valued multiplicity
invariant compatible with the HNN letter, or a simultaneous
coordinate-commutant recovery theorem stronger than ordinary spectral-gap
recovery.  None of this is used by the unconditional non-MF proof.

### 2026-08-13: differential audit from non-MF to nonhyperlinearity

`NON_MF_TO_HYPERLINEAR_DIFFERENTIAL_AUDIT.md` records the repository-first
comparison.  The literal MF-radical mark cannot be upgraded to a tracial
kill because an explicit CE model sends it to `-1`.  The direct surviving
descendant is the Leavitt--Steinberg HS-stability fork.  Its first live,
not-already-refuted input is finite-multiplicity coefficient extraction, not
generic commutant recovery.  The semantic endpoint is now Lean-checked:
a nonidentity member of `hyperlinearResidual` implies `¬ IsHyperlinear`.

### 2026-08-13: the Kun--Thom Clifford phase has no quantitative loss

The finite-coordinate endpoint in `TRUE_KUN_THOM_CLIFFORD_PHASE.md` is now
closed quantitatively.  For involutive unitaries `C,D`, the second-commutator
matrix `X=DCDC` satisfies the exact factorization
`D(CD+DC)C=X+1`; hence
`hsDistSq(X,-1)=hsNormSq(CD+DC)`.  This is Lean-checked in
`Sofic/CliffordPhaseExtraction.lean`.  Therefore the sole remaining content
of the Clifford route is constructing the almost-`Gamma`-central,
anticommuting pair; no error-propagation or phase-detection estimate remains.
The scalar endpoint is now wired to the radical collision as well:
`negOnePhase_detects` and
`exists_hyperlinear_not_isSofic_of_negOnePhase_soficInvisible` are checked in
`Sofic/AntipodalRadicalCollision.lean`.

### 2026-08-13: antipodal conjugacy is a quantitative trace certificate

`TRUE_ANTIPODAL_TRACE_EXTRACTION.md` closes the local analytic step of the
antipodal route.  For finite matrices, unitary `S` and arbitrary `U` satisfy
`4 |tr(U)|^2 <= ||SUS*+U||_2^2`.  Exact antipodality therefore forces trace
zero, and a unitary `U` then has squared Hilbert--Schmidt distance exactly `2`
from the identity.  All three statements are Lean-checked in
`Sofic/AntipodalTraceExtraction.lean`.  The induced ultraproduct detector and
the final sofic-radical collision theorem are Lean-checked in
`Sofic/AntipodalRadicalCollision.lean`.  The remaining gate is wholly global:
derive or compatibly recover an asymptotically antipodal pair from the marked
group relations.

### 2026-08-13: `SL2F13` radical implantation and extension audit

`SL2F13_RADICAL_APPLICATION_AUDIT.md` credits the exact arithmetic and GAP
certificates in `eekarabiyik/SL2F13` and extracts a valid general application:
amalgamating the marked MF-radical involution with a normal generator of a
group `A` implants the whole embedded copy of `A` into the MF radical.  For
`A=PSL(2,13)` this gives a concrete inverse-Galois-labelled finite simple
radical subgroup.  The radical propagation step is Lean-checked in
`Sofic/NormallyGeneratedMFObstruction.lean`.

The direct hyperlinear splice is now closed algebraically.  If a perfect
group is normally generated by `a`, every homomorphism sending `a` to a
central target element is trivial.  Hence the CE detector of the literal
non-MF group, in which `w=-1` is scalar, cannot extend across the amalgam
identifying `w` with a normal generator of `PSL(2,13)`.  See
`FALSE_PERFECT_RADICAL_IMPLANTATION_CANNOT_CARRY_SCALAR_PHASE.md`; the general
lemma is Lean-checked in `Sofic/NormallyGeneratedMFObstruction.lean`.

There is nevertheless a balanced repair, recorded in
`TRUE_BALANCED_RADICAL_IMPLANTATION_IS_CE_VISIBLE.md`.  Direct-sum the scalar
`w=-1` detector with the trivial `w=+1` sector in equal trace, identify the
resulting balanced `C^2` with the involution algebra in the regular
representation of the attached finite group, and take the reduced tracial
amalgam.  Brown--Dykema--Jung's hyperfinite-amalgam theorem makes the target
CE.  Hence for `A=PSL(2,13)` the whole embedded simple group lies in the MF
radical while its intersection with the hyperlinear radical is trivial.  The
abstract detector step is Lean-checked in `Sofic/RadicalSeparation.lean`.
This strengthens MF-versus-hyperlinear separation but still does not create
the required sofic-versus-hyperlinear radical collision.

The same audit corrects the tempting proof that the original Clifford witness
`W` is sofic merely because it is locally-finite-by-residually-finite.  That
reverses Elek--Szabo's extension theorem.  A specific repair does identify the
finite-stage/direct-limit tower with the original coset witness: its dilation
site set is the transitive `V`-set `V/Gamma`.  Hence `W` really is finitely
generated, locally-finite-by-residually-finite, sofic, and non-MF, but for this
special tower reason.  None of these operator-norm applications closes the
hyperlinear trace-selection gate.

### 2026-08-13: alternating Reynolds contracts to scalars

`FALSE_ALTERNATING_REYNOLDS_CONTRACTS_COEFFICIENT_SIGNAL.md` computes the
exact spectrum of `E_A E_(P')` on the five raw coefficient atoms:
`1,19/64,11/64,11/64,1/16`.  Thus the scalar identity is the only common
fixed direction, and every centered signal contracts at rate at most
`19/64`.  The exact diagonalization and invertible eigenbasis are Lean-checked
in `Sofic/CoefficientAlternatingReynolds.lean`.  Finite packet averaging
cannot supply simultaneous coefficient recovery; a nonfinite cross-chart
module is essential.

### 2026-08-13: an explicit infinite-order cross-chart direction

`TRUE_MIXED_COMMUTATOR_HAS_INFINITE_ORDER.md` proves that
`h=[U*X_1U,raw]` has infinite order.  Its Leavitt expansion has a unique
minimum-degree term `s_00 t_(00(10)^4)`; the minimum component of `h^n` is
`s_00 t_(00(10)^(4n))`, of degree `-8n`.  The first sixteen nonzero
coefficient-cut translates have overlap `1/64=tau(F)^2`, so this is a
bilateral mixing direction rather than an orthogonal wandering-projection
contradiction.  Both generating involutions conjugate `h` to `h^(-1)`; the
generic identity is Lean-checked in `Sofic/MixedCommutatorDihedral.lean`.
Therefore `h` alone cannot furnish the missing one-sided module.

### 2026-08-13: transported Pauli orbit has a canonical fingerprint

`TRUE_TRANSPORTED_PAULI_ORBIT_FINGERPRINT.md` computes the full orbit of one
raw coefficient cut under the transported order-32 Pauli packet.  The orbit
has size 16 and its average has raw expectation weights
`75/256,31/256,15/256,15/256`.  The unique top cut is recovered by a fixed
quadratic polynomial with spectral gap `11/64`, formalized in
`Sofic/DoublePauliCoefficient.lean`.  This removes permutation ambiguity once
simultaneous coordinate recovery exists, but does not prove coefficient-space
membership.  The same audit isolates `[X'_1,raw]` as the first mixed word
outside the finite packet; the following entry proves it has infinite order
and records why its dihedral symmetry does not close the endpoint.

### 2026-08-13: the full raw/comb finite intersection is trivial

`FALSE_RAW_512_COMB_INTERSECTION_IS_TRIVIAL.md` closes the finite-Reynolds
shortcut to coefficient membership.  The full raw double-Pauli closure and
its comb conjugate both have order `512`, but their exact intersection is the
identity.  Therefore separate finite-subgroup exactification cannot align the
coefficient spaces; the missing `15/128` membership theorem must use genuine
cross-chart kernel relators or a recovered multiplication module.

### 2026-08-13: coefficient expectation gap `15/128`

`TRUE_COEFFICIENT_EXPECTATION_GAP.md` weakens the final alignment hypothesis.
For every transported character cut `G`, its Hilbert--Schmidt projection onto
the raw four-character coefficient space is `q/8`, while
`hsNormSq(G-q/8)=15/128`.  The identity is Lean-checked in
`Sofic/DoublePauliCoefficient.lean`.  It now suffices for simultaneous
finite-multiplicity recovery to put one transported cut asymptotically in the
raw coefficient space; no permutation or minimal-cut matching is needed.

### 2026-08-13: audited closure boundary for coefficient alignment

`FALSE_EXISTING_REYNOLDS_DOES_NOT_ALIGN_COEFFICIENT_C4.md` verifies that the
current property-`(T)`/finite-average library does not prove the simultaneous
raw/comb `C^4` alignment.  The relative implementer has a fixed Reynolds norm
deficit, so there is no already-commuting ultraproduct element to lift.  The
terminal endpoint has a generous strict margin: trace-flat cuts satisfy
`hsDistSq=7/32>1/8`, kernel-checked in
`Sofic/DoublePauliCoefficient.lean`.  The missing theorem must recover both
finite multiplicity algebras in compatible coordinates and align one pair
below squared distance `1/8`, or prove invariance of the trace-`1/120`
spectral fallback.

### 2026-08-13: trace-flat spectral floor `1/120`

`TRUE_TRACE_FLAT_BLOCK_SPECTRAL_FLOOR.md` removes two more analytic losses.
For every trace-flat comb block, truncating `FGF` above eigenvalue `1/16`
retains trace at least `1/120` and gives singular values at least `1/4`.
The rational endpoint is Lean-checked in
`Sofic/DoublePauliCoefficient.lean`.  Thus the spectral version of `(RPC128)`
now has one structural gate: make the retained cut invariant under the
recovered multiplication arrows.  Density and condition number no longer
need separate recovery arguments.

### 2026-08-13: fixed `7/32` coefficient anti-normalizer gap

`TRUE_DOUBLE_PAULI_COMB_ANTINORMALIZER_GAP.md` turns the constant overlap table
into an exact terminal separation.  Every raw coefficient character cut and
every comb-transported character cut have squared HS distance `7/32`.  The
formula and constant are Lean-checked in `Sofic/DoublePauliCoefficient.lean`.
Thus any simultaneous finite-multiplicity recovery which aligns the two
four-dimensional coefficient algebras (necessarily by a permutation of
minimal cuts) immediately contradicts the canonical trace.  The remaining
gate is precisely that comb-compatible coordinate alignment; abstract group
relations cannot imply it because the regular representation realizes the
anti-normalizer gap exactly.

### 2026-08-13: the comb is Fourier-flat on the coefficient packet

`TRUE_DOUBLE_PAULI_COMB_IS_FOURIER_FLAT.md` computes the exact `4 x 4`
transition table between the raw-invariant coefficient characters and their
comb conjugates.  Every character cut has trace `1/8`, every transition block
has squared Hilbert--Schmidt mass `1/64`, and no block vanishes.  This supplies
the fixed positive-density half of the multiplication-module attack and kills
the Hall-zero variant.  It is trace-flat but not a scaled-isometry system:
already one representative has `FGF != F/8`, so singular-value control remains
part of reduced-Fourier extraction.  The projection block-mass identity is Lean-checked in
`Sofic/DoublePauliCoefficient.lean`.  The remaining theorem must force a
one-sided block to vanish only after finite-multiplicity module recovery; the
reverse block then retains the canonical `1/64` mass and violates finite
projection balance.

### 2026-08-13: raw double-Pauli coefficient packet

`TRUE_RAW_DOUBLE_PAULI_COEFFICIENT_PACKET.md` identifies the first exact
multiplication-to-coefficient bridge in the atlas.  The raw compressor turns
the original Pauli packet into a second Pauli packet with a distinct center;
their equal signs cancel into a raw-invariant coefficient `C2^2` on the
trace-half carrier.  The mixed cell has order `256`, its raw-normalized
closure has order `512`, and the two-sheet splice

```text
B_i = ((1-c)/2) A_i + ((1+c)/2) X_i
```

is an involution, commutes with the Pauli coordinates sheetwise, and is fixed
by raw.  The generic splice algebra is Lean-checked in
`Sofic/DoublePauliCoefficient.lean`.  The next exact gate is the off-diagonal
comb action on these coefficient cuts.  A single transported carrier sign
cannot supply it: `FALSE_COMB_TRANSPORTED_SIGN_STAYS_FINITE.md` gives the
finite order-32 countercell and the trivial small-cell comb intersection.

### 2026-08-13: exact two-arrow Pauli transfer packet

`TRUE_PAULI_BRANCH_TRANSFER_PACKET.md` identifies the two raw branch arrows
on the synchronized finite coefficient sector:

```text
E=P Q,       T0=U* P Q,       T1=U* R P Q.
```

They have common initial projection `E`, orthogonal ranges, and range sum
`U* Q U`.  The complete algebra is Lean-checked in
`Sofic/PauliBranchTransfer.lean`.  Since `tau(Q)=1/4` and `tau(E)=1/8`, the
packet is exactly balanced.  The whole atlas contradiction is now the single
containment `U* Q U <= E`.  A direct root-character proof of this containment
is impossible: `ef=f` implies `ell(ef)=ell(f)` but not
`ell(f)=1 => ell(e)=1`.  The remaining proof must recover a positive-density
paired radical quotient (a genuine multiplication module), and use the raw
compressor to identify its carrier with `E`.

### 2026-08-13: the involutive star extension is hyperlinearity-neutral

`TRUE_INVOLUTIVE_STAR_EXTENSION_PRESERVES_HYPERLINEARITY.md` closes the
logical cost of the star synchronizer.  For every involution `psi` of `Q`,
the two-sheet model

```text
q |-> diag(U_q,U_(psi q)),      j |-> [0 I; I 0]
```

proves `Q semidirect_psi C2` hyperlinear exactly when `Q` is.  Different
`C2` sheets have normalized trace zero and hence maximal HS separation;
same-sheet defects are the average of two defects in the old model.  The
exact block identities are Lean-checked in
`Sofic/InvolutiveTwoSheet.lean`.  Therefore the synchronized Leavitt-star
extension is a legitimate target, and star/adjoint compatibility is no
longer a gate.  The remaining atlas gate is strictly multiplication-to-
support: recover the child--parent identity `ef=f` as inclusion of finite
Pauli coefficient supports through the cross-root Steinberg relations.

### 2026-08-13: double-Clifford cancellation for the Kun--Thom group

`TRUE_DOUBLE_CLIFFORD_KUN_THOM_REDUCTION.md` proves that two identical
Clifford systems cancel their fermionic signs: `a_x=c_x tensor c_x` are
commuting independent Haar lamps. Hence the full Kun--Thom Bernoulli crossed
product embeds trace preservingly in the diagonal tensor-square Clifford
crossed product. CE of one permutation-Clifford crossed product already
makes the explicit Kun--Thom nonsofic wreath product hyperlinear. The exact
remaining gate is coherent Bogoliubov innerness; tensor squaring cancels the
spin cocycle but not finite-mode permutation defects.

### 2026-08-13: local BCS spectral exclusion cannot be groupified

The restriction of a group's regular representation to any finite subgroup
is a sum of regular representations. Hence every character of a commuting
involution subgroup occurs with positive canonical trace, including in any
compatible finite central-character corner. A local group gadget cannot
forbid an arbitrary Boolean assignment without algebraically collapsing the
subgroup; for commuting involutions the resulting constraints are affine.
See `FALSE_LOCAL_BCS_SPECTRAL_EXCLUSION_BY_GROUP_RELATIONS.md`.

### 2026-08-13: mixed-gap/sparse-kernel Iwahori dichotomy

Projecting the identity matrix onto the exact mixed edge-intertwiner space
gives a quantitative dichotomy. If the mixed Laplacian gap collapses, the
remaining obstruction is an almost-invariant vector for the virtually-free
edge. If the gap stays above `kappa`, polar decomposition exactly matches
the two edge representations off invariant kernel/cokernel spaces of
relative dimension at most `delta^2/kappa`. A negative sequence must then
carry a sparse restriction-semiring mismatch which cannot be extended
through the two index-three vertices. See
`TRUE_IWAHORI_MIXED_GAP_DICHOTOMY.md`.

### 2026-08-13: three-player XOR has the same completeness gate

Vidick's earlier three-player XOR reduction does not avoid the LCS
perfect-completeness problem. Its honest strategy wins with probability
exactly `1-epsilon`, while the soundness extraction is proportional to
`epsilon^3`; setting the noise to zero makes soundness vacuous. See
`FALSE_THREE_PLAYER_XOR_PERFECT_COMPLETENESS.md`.

### 2026-08-13: algebraic-Haar transfer criterion

If a non-CE p.m.p. action can be realized as an action by automorphisms of a
compact abelian group with Haar measure, Fourier transform identifies its
crossed product with the group factor of a discrete semidirect product.
That semidirect product is then nonhyperlinear. Manzoor's non-co-hyperlinear
IRS does not yet meet this criterion: its GNS trace records stabilizer
probabilities, its compact realization carries an arbitrary invariant
measure, and isotropy is essential. See
`ALGEBRAIC_HAAR_NONCE_TO_NONHYPERLINEAR.md`.

For Manzoor's free group this route is actually impossible: a Haar
algebraic action has crossed product `L(A semidirect F_r)` with `A`
abelian, and `A semidirect F_r` is sofic by amenable-kernel extension
closure. Thus its group factor is CE and cannot contain the non-CE IRS
algebra trace-preservingly.

### 2026-08-13: robust spectral gap does not repair the Iwahori edge

The natural attempt to apply Dogon--Vigdorovich's robust spectral-gap
theorem to the approximate Iwahori intertwiner is circular. The mixed
left--right action is an exact representation only of the virtually-free
edge group, which has no uniform spectral gap. The ambient adjoint
almost-representation fixes the scalar identity vector tautologically, so
its robust spectral gap does not produce an edge intertwiner. Moreover the
Hilbert--Schmidt robust theorem only removes middle spectral mass and does
not open an exact kernel. The remaining theorem must directly control the
mixed edge action or the explicit high-dimensional flag coordinates. See
`FALSE_ROBUST_T_IWAHORI_EDGE_REPAIR.md`.

### 2026-08-13: the literal non-MF mark is sofic- and CE-visible

The marked word in the explicit ascending-HNN non-MF group does not lie in
the hyperlinear radical.  The finite tower

```text
X_n=Gamma/beta^n(Gamma)
```

supports a tracial Clifford crossed product which is an increasing union of
Connes-embeddable finite-level crossed products.  The doubling injection
extends to a trace-preserving endomorphism; its automorphic dilation and the
crossed product by `Z` remain CE.  With the stable-letter implementer `U`,
the assignment

```text
c=U^* C_(beta(Gamma)) U
```

represents every literal defining relation and sends

```text
w=[t c t^(-1),a t c t^(-1) a^(-1)]
```

to the scalar `-1`.  Therefore

```text
w in Rad_MF(E) minus (Rad_hyp(E) union Rad_sof(E)).
```

The extra sofic detector comes from the group-level tower.  Each finite-level
Clifford semidirect product is a finite extension of `Gamma`; their directed
union is sofic, its automorphic direct limit is sofic, and the final quotient
is the amenable group `Z`.  The literal map sends `w` to the surviving
central Clifford sign.  This is a genuine operator-norm versus sofic/tracial
radical separation, but it is not a hyperlinear-nonsofic group because the
marked word is specifically not in the sofic radical.  In particular the
exact `M_16` spin block in the negative corner is real but cannot close a
contradiction; the CE model realizes that block exactly.  Full proof and scope:
`notes/TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md`.

The detecting image is a finitely generated sofic non-MF group.  Embedding it
in a countable simple sofic group by Elek--Szabó and using portability makes
the entire MF radical of that simple group equal to the group.  This is a
strong operator-norm/tracial separation, but the envelope is still sofic.
The complementary collision remains the exact universal target:

```text
x in Rad_sof(H) but x notin Rad_hyp(H).
```

The Lean theorem
`not_soficResidual_le_hyperlinearResidual_of_detector` records this
noncontainment, and
`hyperlinear_range_and_failureOfSoficity_of_soficInvisible` extracts the
hyperlinear nonsofic detecting range.

The direct index-to-phase replacement also closes negatively.  For every
finite coordinate, `PUP:PH->PH` is a square operator, so its Fredholm index
is zero; equivalently `P` and `UPU^*` are already Murray--von Neumann
equivalent and have zero `K_0` difference.  The same trace-index calculation
holds in every finite von Neumann algebra.  A nonzero index would require
extra asymmetric boundary data not supplied by the group relations.  See
`notes/FALSE_KAZHDAN_COMPRESSION_INDEX_TO_PHASE.md`.

The de la Harpe--Skandalis determinant does not automatically restore that
missing phase in normalized Hilbert--Schmidt models.  For
`u_d=diag(-1,1,...,1)`, one has `||u_d-1||_2=2/sqrt(d)->0`, but the principal
normalized logarithm satisfies

```text
2L_d(u_d)-L_d(u_d^2)=1/d.
```

The sequence `(1/d)` is nonzero in `c_0/c_00`, so the logarithm is not
additive on the HS-null subgroup with values in the coefficient group which
retains microscopic winding.  Modding out by the normalized `K_0` lattice
repairs additivity but kills exactly this index/parity class.  Thus the
operator-norm central-extension theorem of Dadarlat--Glebe cannot simply be
ported to the tracial matrix ultraproduct.  See
`notes/FALSE_DETERMINANT_INDEX_TO_PHASE_HS_EXTENSION.md`.

Topologically, the HS-null unitary subgroup is path connected: principal
logarithms give the path `u_n(t)=exp(t log u_n)`, and the logarithms remain
HS-null by `|theta|<=(pi/2)|exp(i theta)-1|`.  Therefore every continuous
discrete phase on that kernel is trivial.  Any surviving parity must be a
discontinuous invariant protected by additional presentation relations.
The determinant square-root cover cannot be descended either: the HS-null
rank-one loop `diag(exp(2 pi i t),1,...,1)` has odd determinant winding, so
its lift closes at the opposite central sign.  Hence the cover has no
continuous splitting over the subgroup which must be killed in the tracial
quotient.

The active collision target is therefore unchanged on the Kun--Thom side:
retain one explicit element of `Rad_sof` in a CE representation.  The
smallest current form is CE of the one-orbit parity corner

```text
pL(J) *_pL(K) (pL(K) crossed_alpha C_2),
```

equivalently CE of the negative central corner of `H_theta`.  Large repeated
edge multiplicities can support relative randomization only after compatible
vertex restrictions have been constructed.  Exact finite-dimensional
vertex representations are already ruled out by the Kazhdan matching gap,
and matrix amplifications of the canonical regular vertex have a uniform
twisted-innerness gap.  Hence multiplicity amplification does not by itself
supply the missing edge-compatible embedding.  The exact quotient-block
calculation and the surviving nonmonomial inclusion theorem are recorded in
`notes/FALSE_RELATIVE_RANDOMIZATION_NEEDS_EDGE_TRACE_MODEL.md`.

### 2026-08-12: consolidated outcome — three exact gates remain open

The current investigation does not prove that Thom's group `K` is nonsofic
and does not produce a hyperlinear nonsofic group.  Its complete synthesis is
now preserved in
`notes/HYPERLINEAR_NONSOFIC_RESEARCH_OUTCOME_2026_08_12.md`.

For `K`, the Prüfer tower forces divisibility of favorable centralizer
orbits, and the root-commutator structure strengthens this to a `p^(2m)`
divisibility constraint on repaired level-`m` sectors.  Neither statement
controls normalized orbit size.  The exact missing theorem is a
fiber-compatible matching of a sofic model with the amplified model obtained
from `K/F_m~=K`, equivalently uniform approximate coboundary trivialization
of the finite extension cocycles.  Property `(T)`, self-quotienting, and
product/balanced amplification do not supply it.

The strongest general converter is the finite-central-radical corner
theorem: one weak-MF group with a nontrivial finite-order element in
`Z(E) intersect Rad_sof(E)` would have a hyperlinear nonsofic image after
spectral compression.  The Clifford cover is norm-MF sterile, while the
shear cover's required antipodal compatibility is already the missing
norm-to-trace breakthrough.

The weak-MF Kun--Thom symmetric double remains blocked by trace selection.
Its radical witness is operator-norm visible in the canonical Kazhdan
corner, but Shulman's strong-* representation lifts do not force that corner
to occupy positive normalized matrix rank.  The three live gates are
therefore: relative matching for `K`, a weak-MF finite central-radical group,
or a trace-visible matrix profile for the symmetric double.

### 2026-08-12: a first-order radical jet is already a complete FALSE certificate

The quadratic trace-gap amplifier has a strong geometric consequence.  Let
`K=<S|R>` be finitely presented, let `1!=q in Rad_sof(K)`, and let `rho` be
a finite-dimensional unitary representation.  If a skew-Hermitian tangent
at `rho` kills the derivatives of every defining relator but moves `q`,
then the generator perturbation has relation defect `O(t^2)` while

```text
1-Re tr(phi_t(q)) asymptotic c t^2,       c>0.
```

Thus `eta_t^2/kappa_t=O(t^2)->0`, and the phase-cancelled tensor theorem
produces a hyperlinear image retaining `q`; that image is nonsofic.  No
integration of the tangent is needed.

For a folded double this reduces to one honest finite-dimensional
representation with `rho(h)` outside the bicommutant of `rho(Gamma)`.
The obstruction for the current infranormal Kun--Thom pair is actually
complete: property `(T)` makes both vertex tangents inner, agreement on the
edge leaves a finite-dimensional `Gamma`-intertwiner, and infranormality
propagates that intertwiner through the whole normal closure `N`.  Hence
every tangent at every finite-dimensional representation kills every fold
difference `i_2(n)i_1(n)^(-1)`, `n in N`, and therefore the complete sofic
radical.  This closes every full-presentation finite-dimensional linear
search on the current symmetric double, not merely the same-model ansatz.

The criterion still changes the atlas stopping rule: quadratic obstruction
of a tangent is irrelevant once the tangent satisfies the full presentation.
The current outer `A_8` tangent satisfies only the 24 certified local zero
classes, so it remains insufficient.  Full theorem and scope:
`notes/FALSE_QUADRATIC_RADICAL_JET_CRITERION.md`.

The statement extends to every finite order.  If defining relators are
`O(t^(m+1))` and a radical word first moves at order `t^m`, then squared
defect divided by trace gap is still `O(t^2)`.  Conversely the current
double is fixed-dimension sterile at every such order: formal property-`(T)`
rigidity conjugates each vertex jet back to an exact vertex representation,
and the edge Kazhdan projection plus infranormal intertwiner propagation
forces agreement on the full normal closure `N` to the same order.  Thus
Jacobian, Hessian, and higher formal searches on fixed-dimensional
representations of this double are closed; a live jet must have growing
dimension or a different radical presentation.

This sterility is inherited by the usual descendants.  Tangents pull back
through quotients and restrict through overgroups, while a cocycle which
kills a kernel element kills its entire normal closure.  Hence radical
abelianization, bounded-exponent quotients, central-shear gadgets, and other
repackagings of the same Kun--Thom radical cannot manufacture the missing
jet.  A fixed-dimensional jet attack needs a genuinely different source of
nonsoficity.

The necessary growing-dimensional replacement has one exact finite
statistic.  For an operator-norm microstate put

```text
A_n=phi_n(q)-1,
r_eff(A_n)=||A_n||_F^2/||A_n||_op^2.
```

The phase-cancelled amplifier succeeds if

```text
epsilon_n^2 d_n/||A_n||_F^2 ->0,
```

or, under a fixed operator wall, if

```text
epsilon_n sqrt(d_n/r_eff(A_n))->0.
```

This interpolates rank-one square-root loss and positive-density trace
visibility.  Exact finite-dimensional ambient `G`-sectors cannot satisfy
it by the Kazhdan matching inequality; a successful Shulman coordinate must
therefore exhibit genuine ambient Frobenius instability.  Full theorem and
the required reporting tuple are in
`notes/FALSE_WEAK_MF_EFFECTIVE_RANK_PROFILE.md`.

### 2026-08-12: phase-cancelled tensors lower the FALSE threshold by one power

The one-number relative-commutant criterion has been sharpened.  Given
finite-window maps with multiplication defect `eta_n` and marked radical
trace gap `kappa_n`, first replace each map by

```text
phi_n directSum conjugate(phi_n) directSum 1 directSum 1.
```

Every relative relation trace is then real and belongs to `[0,1]`.
Taking an `L_n`-fold tensor power makes relation defects grow only as
`sqrt(L_n) eta_n`, while the marked trace decays like
`exp(-L_n kappa_n/2)`.  Hence the sufficient hypothesis is

```text
eta_n^2/kappa_n -> 0,
```

not the previously recorded `eta_n/kappa_n->0`.  For the Haar
relative-commutant scalar this becomes

```text
epsilon_n^2/Delta_n -> 0,
Delta_n=dist_2(x_n,W_n)^2.
```

Thus relation defect need only be little-oh of the Hilbert--Schmidt seam
size.  In particular, if an active corner has trace `r_n`, carries an
order-one marked wall, and has active relation amplitude `alpha_n->0`, then
the criterion holds regardless of how fast `r_n->0` because
`epsilon_n^2/Delta_n=O(alpha_n^2)`.  Small-corner dilution with arbitrary
order-one boundary completion is still sterile, but every genuinely
convergent active covariance model is back in scope.  Full proof:
`notes/FALSE_ONE_NUMBER_RELATIVE_COMMUTANT_CRITERION.md`; corrected scope:
`notes/FALSE_TANGENT_ACTIVE_CORNER_DILUTION_NO_GO.md`.

### 2026-08-12: paper-level explicit finitely presented non-MF group

More generally than the ascending-HNN formulation, let `G` be finitely
presented, let `Gamma<G` be a finitely generated property `(T)` subgroup,
and suppose `t Gamma t^(-1)<Gamma`.  Adjoin an involution `c` centralizing
`Gamma`.  For `a in Gamma-t Gamma t^(-1)`, put

```text
d=t c t^(-1),
w=[d,a d a^(-1)]
```

and impose that `w` is a central involution.  The resulting finitely
presented group `E` has `w!=1`: the coset Clifford semidirect product sends
the two conjugates in the commutator to distinct Majoranas and sends `w`
to the Clifford sign.

Every homomorphism of `E` into a norm-matrix corona kills `w`.  If the
negative spectral corner of `w` were nonzero, the adjoint representation
would place the Kazhdan projection of `Gamma` in a stably finite
norm-matrix corona.  The strict compression gives

```text
P<=Ad(t)P,
```

while unitary equivalence and stable finiteness force equality.  The root
vector `c` is `Gamma`-fixed, so equality makes `d` `Gamma`-fixed and forces
`[d,a d a^(-1)]` to converge to `1` in normalized HS norm.  On the selected
corner the same word is `-1`, a contradiction.

The uniform ascending-HNN source uses a finitely presented Kazhdan group
with a proper injective endomorphism.  The concrete choice

```text
Gamma=Z^3 semidirect SL_3(Z),
alpha(v,A)=(2v,A),
a=(e_1,I)
```

gives an explicit finitely presented non-MF group.  This appears to answer
the universal group-MF conjecture negatively, subject to specialist
literature-priority review.  It does not settle hyperlinearity or the
active hyperlinear-versus-sofic goal.  Full proof and scope audit:
`notes/EXPLICIT_FINITELY_PRESENTED_NON_MF_GROUP.md`.

Formal-status qualification: the unconditional Lean theorem uses an
independently chosen Shalom-cover presentation.  Lean checks the literal
eight-generator presentation and its nontrivial marked word, but its
operator-MF conclusion still awaits an internal property `(T)` proof for the
raw presented base.

For a Kun--Thom Kazhdan infranormal pair the same marked word satisfies the
stronger statement

```text
w in Rad_sof(E).
```

Given an arbitrary map from `E` to a sofic group, pair it with the
retraction `E->G`; the restriction to the diagonal copy of `G` is then a
sofic representation.  Kun--Thom centralizer normalization sends
`d=tct^(-1)` into the centralizer of `Gamma`, so it kills
`w=[d,a d a^(-1)]`.  Consequently the active FALSE endpoint needs only one
CE negative character: find a CE tracial representation `pi` of `G` and a
`Gamma`-central involution `C` such that

```text
[pi(t)Cpi(t)^*, pi(a)pi(t)Cpi(t)^*pi(a)^*]=-1.
```

This is strictly weaker than embedding the full CAR crossed product: only
one anticommuting orbital edge is prescribed.  A solution gives a
hyperlinear image retaining the full-sofic-radical word `w`, hence a
hyperlinear nonsofic group.

Equivalently, seek an orthogonal representation `rho:G->O(H_R)` with a
`Gamma`-fixed unit vector `xi` and

```text
<rho(t)xi,rho(a t)xi>=0,
```

whose Bogoliubov CAR crossed product is Connes embeddable.  The
quasi-regular representation on `ell2(G/Gamma)` has the required geometry.
Any successful `rho` is necessarily infinite dimensional and not weakly
contained in the regular representation: finite dimension makes the nested
Kazhdan fixed spaces equal, while weak regularity plus a `Gamma`-fixed
vector would force `Gamma` amenable.  Alekseev--Bradford's halo/graph
permanence does not prove CE here, because it requires the underlying
coset/graph action to be sofic, exactly what the Kun--Thom example forbids.

### 2026-08-12: Iwahori counterexamples require high-dimensional type escape

The fixed-library theorem for the Dogon--Vigdorovich matching problem
extends to every dimension-tight sequence.  If, on even one modular vertex,
all but `epsilon d_n` dimensions lie in irreducible summands of dimension at
most a fixed `D(epsilon)`, then the limiting vertex trace is a direct
integral of finite-dimensional traces and hence amenable.  Character
rigidity for `SL_2(Z[1/2])` excludes the only nonamenable central-regular
summands, and hyperfinite HS stability corrects the whole Iwahori asymptotic
representation.

Hence a negative sequence must place a fixed positive fraction of its
dimension in irreducible `SL_2(Z)` summands escaping every dimension bound,
on both vertices.  Continuous motion through bounded-dimensional types is
not an escape.  The remaining target is uniform high-dimensional
restriction theory for the index-three Iwahori inclusion.  See
`notes/TRUE_IWAHORI_MATCHING_FIXED_TYPE_REDUCTION.md`, Theorem 6.

### 2026-08-12: the negative Clifford corner closes the norm-MF route

The canonical projection `e=(1-z)/2` does remove relative-rank blindness:
inside the renormalized `z=-1` matrix corner, distinct Clifford lamps have
squared normalized-HS distance `2`.  This does not supply an MF-to-CE
conversion for the Kun--Thom Clifford group.  In fact every homomorphism of
that group into a norm quotient of matrix algebras kills `z`.

The proof cuts to the negative corner, uses conjugation on the normalized
matrix Hilbert spaces, applies the Kazhdan projection to the strict
compressor, and invokes stable finiteness to make the compressor preserve
the `Gamma`-fixed subspace.  Two distinct Clifford sites are then forced to
agree in `L2`, contradicting their exact anticommutation.  Thus the desired
operator-norm MF hypothesis is false, not merely unproved.  Also, a central
corner of an arbitrary faithful norm representation need not itself remain
faithful on every group element.

The direct tracial target remains the Connes embeddability of the negative
CAR crossed product.  Full proof: `notes/FALSE_CLIFFORD_NORM_MF_STERILITY.md`.

### 2026-08-12: matrix exponents make the marked compressor orbit free

The large external stabilizer in the standard exponent lattice is not
intrinsic to the Kun--Thom construction.  Put

```text
V=M_d(Z),  C=M_d(N),
R_+=F_q[C],  R=F_q[V],
Gamma=E_r(R_+),  G=E_r(R) semidirect SL_d(Z),
```

with `SL_d(Z)` acting on exponent matrices by left multiplication.  This is
again a residually finite Kazhdan nonnormal infranormal pair; the same
positive nonnegative-matrix semigroup compresses `Gamma`, and the positive
Bernoulli core remains sofic because every compressed coefficient monoid is
free polynomial and every positive stabilizer is congruence separable.

For `t=I+E_12` and `gamma=e_12(y^I)`, the predecessor has exponent
`t^(-1)I=I-E_12`, so it is genuinely Laurent, while `t^nI=I+nE_12` is
positive for every `n>=0`.  Unlike a standard exponent vector, `I` has
trivial external stabilizer.  The marked orbit is therefore the regular
`SL_d(Z)`-set: there is no stabilizer cocycle and no stabilizer intertwiner
left in the marked Fourier transport.

This does not yet construct the required nonliftable vertex maps.  It
removes one independent obstruction and localizes the remaining theorem to
compatibility with the finite positive ring/elementary window on regular
external charts.  Congruence quotients make the marked orbit exactly regular,
but still absorb `I-E_12` as the positive exponent `I+(m-1)E_12`; thus the
gain is removal of stabilizer holonomy, not removal of the finite-ring
absorption theorem.  Full proof and exact endpoint:
`notes/FALSE_FREE_MARKED_ORBIT_AMPLIFICATION.md`.

### 2026-08-12: the Ioana shortcut has a free-action scope gap

The coherent-Schreier note needed one further correction.  Ioana's
profinite cocycle-superrigidity theorem (`arXiv:0805.2998`) is stated for a
**free ergodic profinite action**.  The natural inverse limit of the finite
coset actions in the clock construction is nonfree: it retains conjugates
of the amenable stabilizer.  Thus profiniteness and ergodicity alone do not
authorize the application.

The bounded-moment implication remains valid conditionally if one first
constructs a free profinite realization carrying a coherent
`BS(1,p+1)`-valued lift, or proves a suitable nonfree rigidity theorem.
Neither bridge currently exists, and the primitive scalar system is in any
case excluded by the Kazhdan moment lower bound.  The live globalization
route is therefore the amenable-stabilizer **local orbit-chart** theorem,
which genuinely applies to nonfree set actions, together with a
chart-functorial matrix-valued fiber assignment.  Updated scope:
`notes/FALSE_IOANA_COHERENT_SCHREIER_LIFT_CRITERION.md` and
`notes/FALSE_IOANA_DRIMBE_SCHREIER_SCOPE_AUDIT.md`.

### 2026-08-12: finite fold kernels have an exact relative-abelian carrier

For the fold `r:D=G *_Gamma G->G` and a quotient `q:G->Q` with kernel `N`,
the kernel `K=ker(qr)` splits as `F semidirect N`, where

```text
F_ab = I_(G/Gamma),
K_ab = (I_(G/Gamma))_N directSum N_ab.
```

If the positive image is all of `Q`, then `N` is transitive on `G/Gamma`
and

```text
(I_(G/Gamma))_N = N/([N,N](N intersection Gamma)).
```

The marked fold word is represented by `h gamma^(-1)` in this relative
abelianization.  In the natural period quotient `x^M=1`, take

```text
h=e_12(x^(-1)),  gamma=e_12(x^(M-1)),  t=x^M-1.
```

The discrepancy `n=e_12(-x^(-1)t)` differs from the positive kernel element
`u=e_12(-x^(M-1)t)` by the single commutator

```text
n u^(-1)=e_12(x^(-1)t^2)
         =[e_13(t),e_32(x^(-1)t)].
```

Thus the finite fold class already vanishes in ordinary relative
abelianization.  This replaces a large exact homology calculation by one
Steinberg relation and explains the natural finite-clock absorption
conceptually.  It does not kill the asymptotic branch cut: `u` and its word
expression grow with `M`.  The sole remaining statistic is the metric cost
of distributing that growing filling over fixed presentation coordinates.
Full proof: `notes/FALSE_FOLD_KERNEL_RELATIVE_ABELIANIZATION.md`.

### 2026-08-12: an amenable relative core cannot hide the wall

A tempting completion of the relative-bicommutant endpoint is now closed.
If a CE representation `pi:G->U(M)` made `N=pi(Gamma)''` amenable while
leaving `pi(h)` outside `N`, then the amalgam

```text
M *_N (N tensor M_2)
```

would be CE by hyperfinite amalgamation.  Its matrix flip would centralize
`Gamma`, and amalgamated freeness gives the exact identity

```text
||[v,pi(h)]||_2^2=2 dist_2(pi(h),N)^2,
```

finishing FALSE.

This configuration is impossible.  Property `(T)` makes every amenable
factorial `Gamma`-trace finite-dimensional; finite-dimensional local
rigidity makes the center of `N` atomic.  Conjugation by a compressor is a
trace-preserving endomorphism of this atomic finite type-I algebra.  Its
factor multiplicities define a stationary Markov chain along which matrix
dimension can only increase.  Stationarity forces constant dimension, so
the chain reduces to deterministic finite cycles and every fiber map is
onto.  Therefore the compressor normalizes `N` and every inverse predecessor
lies in `N`.

Thus every live relative wall has a **nonamenable** relative core and must
be genuinely extrinsic/nonliftable.  Full proof:
`notes/FALSE_AMENABLE_RELATIVE_CORE_NO_GO.md`.

The complementary nonamenable construction is now exact for one
compressor.  For an injective endomorphism `beta:Gamma->Gamma`, the coset
tower

```text
X = disjointUnion_(n>=1) Gamma/beta^n(Gamma)
```

supports a Bernoulli crossed product `N=A rtimes Gamma` and a
trace-preserving endomorphism extending `beta`.  The root lamp lies in
`alpha(N)' intersect N` and has squared commutator norm exactly `2` with
every `gamma` outside `beta(Gamma)`.  The automorphic dilation converts it
into the required exact relative wall for the ascending HNN subsystem, and
is CE whenever `N` is CE.  The remaining scope issue is sharp: Kun--Thom's
sofic-radical theorem uses the full infranormal vertex, whereas the ascending
subsystem need not be infranormal.  See
`notes/FALSE_COSET_TOWER_AUTOMORPHIC_DILATION.md`.

The one-compressor picture globalizes algebraically over the entire
compression semigroup.  If `S=P_Gamma` and

```text
X_+ = S Gamma/Gamma subset G/Gamma,
N_+ = L^infinity({+-1}^X_+) rtimes Gamma,
```

then every `s in S` acts on `N_+` by a trace-preserving endomorphism and
the full Kun--Thom wreath algebra is generated by `N_+` and their
automorphic dilators, with all relations among the dilators imposed.  The
root lamp is central in `N_+`, and every strict predecessor has commutator
energy exactly `2` after dilation.  Thus the wall and the radical word are
both settled in the canonical nonsofic wreath group.  The remaining theorem
is precisely CE preservation for this simultaneous nonamenable semigroup
dilation; individual compressor dilations preserve CE, but coupling them
over `N_+` is the unresolved nonamenable-amalgamation step.  See
`notes/FALSE_FULL_COMPRESSION_SEMIGROUP_DILATION.md`.

The most obvious semigroup-dilation shortcut is now closed.  In the explicit
monomial-cone pair, every compressor has external component in the positive
monoid `SL_3(Z) intersection M_3(N)`.  The two positive transvections
`I+e_12` and `I+e_21` have no common right multiple: their positive column
cones intersect in the codimension-one wall `x_1=x_2`, so a common multiple
would have rank at most two.  Transposition gives the left-hand obstruction.
Thus the full compressor semigroup is neither left nor right Ore and admits
no cofinal Ore subsemigroup.  The simultaneous CE gate is genuine non-Ore
branching, not a missing application of an ordinary group-of-fractions
dilation theorem.  See `notes/FALSE_COMPRESSION_SEMIGROUP_ORE_NO_GO.md`.

There is also a constructive simplification: the nonamenable positive core
can be made **sofic**, so its CE microstates are no longer part of the
unknown.  Take

```text
R_+=F_q[x_1,...,x_d],  R=F_q[x_1^(+-1),...,x_d^(+-1)],
Gamma=E_r(R_+),        G=E_r(R) semidirect SL_d(Z),
T=Gamma (SL_d(Z) intersection M_d(N)).
```

For a positive external compressor `ell`, its orbit stabilizer is
`E_r(F_q[ell N^d])`.  Both coefficient rings are polynomial rings, so
Suslin stability identifies these elementary groups with the corresponding
special linear groups.  Any matrix outside the stabilizer therefore has an
entry outside the monomial subring.  Truncating all monomials above a fixed
degree gives a finite ring quotient which preserves that offending entry,
proving the stabilizer congruence-separable.  Hence the positive action is
sofic, its generalized wreath product is sofic, and the positive Bernoulli
crossed product is CE.  The only live gate is now implementing the positive
endomorphisms simultaneously, with their non-Ore branching and the
relations of `SL_d(Z)`.  Full proof:
`notes/FALSE_POSITIVE_CORE_IS_SOFIC.md`.

The most natural noncommutative-fiber completion is now isolated.  Replace
the commuting `C_2` lamps on `G/Gamma` by Majorana involutions whose distinct
coordinates anticommute.  Algebraically this is a locally finite central
extension `Wtilde` with central involution `z` and

```text
c_x c_y = z c_y c_x  (x!=y).
```

Its quotient by `<z>` is the known Kun--Thom nonsofic wreath group, so
`Wtilde` is automatically nonsofic.  In the central character `z=-1`, it
embeds faithfully into the Clifford crossed product

```text
Cl(G/Gamma) crossed_product G.
```

The root Majorana centralizes `Gamma` and has squared commutator norm `2`
with every strict predecessor.  Hence CE of this one twisted tracial summand
would immediately make `Wtilde` hyperlinear and nonsofic.  This is the sharp
matrix-fiber target.  Ordinary finite cone truncations cannot prove CE:
property `(T)` rules out common Følner exponent sets, and second
quantization does not dilute a defect supported on a fixed number of modes.
See `notes/FALSE_FERMIONIC_KUN_THOM_ENDPOINT.md`.

### 2026-08-12: natural-module formal deformations fail over every field

The all-fields square-zero theorem has an all-order strengthening on the
natural eight-point permutation module. The integral first-order constraint
matrix has rational rank `62` and an exact `62 x 62` minor of determinant
`8192=2^13`. Since the chart commutant `<I,J>` is always a two-dimensional
kernel, it is the entire constrained kernel over every odd field. The first
noncommutant coefficient of any truncated formal deformation would therefore
already contradict the linear equations. In characteristic two the kernel
has one extra projective line, whose nonzero representative is quadratically
obstructed by exact truncated-ring replay. Hence every univariate
`k[epsilon]/(epsilon^N)` deformation on the natural module kills the marked
phase, for every field `k` and every `N`.

This closes “raise the nilpotent order/change characteristic” on the natural
module. It does not close nonlinear analytic branches, other modules,
different chart modules, or different order-zero holonomy. Full theorem:
`notes/FALSE_ATLAS_NATURAL_ALL_FIELD_HIGHER_ORDER_NO_GO.md`.

### 2026-08-12: the inner first-order atlas obstruction holds over every field

The modular certificate is an instance of a general representation-free
principle. At an inner alignment of two finite-group charts, every
square-zero word derivative is a signed prefix element `d_w in k[G]`.
Trivial-word constraints contribute `d_z`, survivor centrality contributes
`(g-1)d_s`, and membership of the marked derivative in their generated left
ideal kills the marked phase in every `k[G]`-module at once.

For the Leavitt `A_8` atlas, exact certificates prove for every field `k`

```text
d_11 in sum_z k[A_8] d_z
        + sum_(s in {11,30,44,55}, g in S)
            k[A_8] (g-1)d_s.
```

The rational certificates use twelve `S_8` Specht restrictions covering all
fourteen complex `A_8` sectors. The representation denominator is `1814400`
and the direct row-certificate denominator is `74129444573184000`, leaving
exceptional prime support `{2,3,5,7,11,13,1181}`. The existing `F_2` regular
group-algebra certificate closes characteristic two. New replayable sparse
regular-algebra DAG certificates close `F_3,F_5,F_7,F_11,F_13,F_1181`; in
each case the phase enters after rank `149`. Rational reduction plus Maschke
semisimplicity closes every remaining prime. Scalar extension then closes
every field, arbitrary modules, indecomposables, multiplicities, and
off-diagonal couplings at the fixed inner square-zero alignment.

This does not prove local unitary rigidity or nonhyperlinearity. The live
atlas branches must be nonlinear/higher-order, leave the inner order-zero
alignment, or separate the chart modules. Changing coefficient
characteristic alone is closed. Full theorem and replay:
`notes/FALSE_ATLAS_FIRST_ORDER_GROUP_ALGEBRA_PRINCIPLE.md`.

### 2026-08-12: Gaussian and free-Gaussian amenable-orbit fibers also collapse

Replacing the Bernoulli fiber over `G/C_G(h)` by either the classical
Gaussian or free Gaussian functor does not create the relative wall.  Since
`C_G(h)` is amenable, the quasi-regular representation is weakly contained
in the regular representation of `G`.  After restriction to every
finite-index subgroup of the nonamenable Kazhdan group `Gamma`, every
nonconstant symmetric- or full-Fock chaos remains weakly regular by Fell
absorption.  Hence it has spectral gap and no fixed vector, including in
the ultrapower.

Combining this with the exact relative FC-centre
`FC_G(Gamma)={+-I_4}` gives, for both Gaussian crossed products,

```text
L(Gamma)' intersect M=L({+-I_4}),
L(Gamma)' intersect M^omega=L({+-I_4}) <= {u_h}'.
```

Thus the amenable orbit cannot be rescued by passing from independent
tensor fibers to either Fock functor.  Any live analytic construction must
use a non-weakly-regular correspondence or an extrinsic commutant in a
larger CE algebra.  Full proof:
`notes/FALSE_AMENABLE_ORBIT_GAUSSIAN_RELATIVE_COMMUTANT_NO_GO.md`.

### 2026-08-12: finite-index Bernoulli tower audit

The affine endomorphism
`alpha(z,A)=(2z,A)` of `Z^3 semidirect SL_3(Z)` gives an exact tower with
indices `8^n`, hence an exact finite-tracial Bernoulli wall.  It does not
give a radical pair: the pair `alpha(Gamma)<Gamma` already has a finite
quasi-regular wall, and the ascending tower group is sofic.  A modular
homomorphism gives the sharper obstruction: a property-(T) group generated
only by strict finite-index compressors of a commensurated subgroup cannot
exist.  Any Kazhdan completion must add infinite-index directions.  The live
theorem is therefore a mixed dilation: extend the local lamp wall over those
directions inside a Connes-embeddable finite algebra, with a non-group
relative-commutant unitary.  Full audit:
`notes/FALSE_FINITE_INDEX_BERNOULLI_TOWER_AUDIT.md`.

The analogous semifinite shortcut is now also closed exactly.  Put the
quasi-regular action in `B(l2(G/Gamma)) tensor A`, take its inner crossed
product, and compress by the finite root projection.  The canonical Morita
cocycle cancels the entire coset coordinate: the corner representation is
just `sigma tensor lambda_G`.  A root-supported element is a relative wall
after compression iff its internal coefficient was already a relative wall
for `sigma`.  Thus proper infiniteness and finite-corner compression do not
supply the missing unitary.  Full proof:
`notes/FALSE_SEMIFINITE_MORITA_COMPRESSION_NO_GO.md`.

The 2025 amenable-near-representation characterization does not close the
negative branch either.  Its amenability is Bekka amenability encoded by a
finitely additive charge on a basis.  Hyperfinite HS stability assumes
amenability of the normalized-trace GNS von Neumann algebra.  The charge may
live on zero normalized density, so the former does not supply the latter.
Property `(T)` only extracts a finite-dimensional summand after one has an
honest amenable representation; it cannot repair the near multiplication
law.  Full scope audit:
`notes/FALSE_AMENABLE_NEAR_REPRESENTATION_SCOPE_AUDIT.md`.

### 2026-08-12: repaired level-169 packet has an exact integral section

The packet-only dual solver was rerun on MSI against the repaired packet
with SHA-256

```text
b9f37304009e64acb829c6c4da5f7f3f7dcbce9996f88b9c8794b147ee90e483.
```

All twelve ambient integer dual equations are solvable.  The projected
packet is a rational basis and the solver reports

```text
complete_integral_section=true,
projected_packet_is_q_basis=true.
```

Thus the parity repair did not merely fix the projected determinant: the
repaired packet really has an integral ambient dual section.  This closes
the qualitative level-`169` lift question.  The HNF completion is not a
quantitative certificate: its first unreduced section has maximum
coefficient about `8.56e47`, full support `3728` in every column, and a
packet Riesz-section upper bound about `2.30e50`.  These values measure the
bad choice of representatives, not an obstruction, because the affine
fiber still permits reduction by the saturated coboundary lattice.  The
live theorem remains a family-uniform, bounded-overlap choice of section.

### 2026-08-12: weak ucp stability sharpens, but does not select, the fork

Dogon's 2023 theorem replaces flexible Hilbert--Schmidt stability by the
strictly weaker weak ucp-stability in the central-extension obstruction.  In
the present project this yields the following exact negative-side target.  If
the known nonsofic Kazhdan quotient `Q` admits cocycles

```text
c_n in Z^2(Q,T),        [c_n]!=0,        c_n(g,h)->1,
```

whose twisted regular algebras `L_(c_n)(Q)` are Connes embeddable, then their
canonical projective regular unitaries are already a trace-separating
normalized-HS asymptotic representation of `Q`.  Hence `Q` is hyperlinear and
nonsofic, proving FALSE.  Weak ucp-stability would contradict this family by
the Nicoara--Popa--Sasyk projective Kazhdan lemma.

This does not presently select a branch.  The explicit Steinberg cover `U`
is a universal central extension and therefore superperfect, so it has no
further non-split central extension detected by `H_2(U,Z)` to which the
criterion can simply be iterated.  For the base `Q`, LLP or weak
ucp-stability is itself the unresolved global lifting problem.  Moreover the
stable/nonhyperlinear branch would construct a nonhyperlinear group, but
would not decide whether every hyperlinear group is sofic.  The CE
twisted-algebra family is therefore the exact projective certificate, but
the prefix theorem below shows that it is not a simpler target than
hyperlinearity of `Q` itself.

The simultaneous audit of character rigidity and robust `(T;CE)` gives no
relative-commutant no-go.  Character data are blind by regular-character
camouflage.  A wall `v in pi(Gamma)' intersect M` is a fixed vector for the
conjugation representation on `L^2(M)`; that representation is not in
general tracial or CE, and even a spectral gap would not replace the finite
dimension argument which turns two nested, unitarily equivalent fixed spaces
into equal spaces.  Thus the extrinsic relative-bicommutant endpoint remains
live.

For the Leavitt witness, prefix homological death makes the twisted-algebra
criterion no easier than the original target.  The injective corner map
`kappa:Q->Q` has `kappa_*=0` on `H_2(Q,Z)`.  Hence every circle-valued
cocycle untwists on `kappa(Q)`, and every twisted regular algebra `L_c(Q)`
contains a trace-preserving copy of `L(Q)`.  Connes embeddability of even one
twist already proves `Q` hyperlinear.  On the universal cover, the lifted
prefix map kills the whole center, so standard prefix replication also
annihilates every genuine atlas phase.  A surviving model must change its
cross-chart holonomy or representation content rather than refine one fixed
phase block.  Full proof:
`notes/FALSE_PREFIX_TWISTED_SUBALGEBRA_RIGIDITY.md`.

For the Leavitt atlas, the authoritative finite phase seed is the explicit
dual-number quotient

`H=(C_2)^7 semidirect A_8`, `|H|=2,580,480`.

It kills all 24 representatives of the 178 currently certified zero
relations, sends survivor `s_11` to the unique nontrivial central involution,
and its negative regular sector restricts on each full `A_8` chart as 64
copies of the regular representation.  This strictly supersedes the earlier
four-relation order-2688 block.  The current boundary is not a set of twenty
uncoupled relations: the 56 uncertified words reduce to the four survivor
classes `s_11,s_30,s_44,s_55`, and the first-order Boolean dual-number family
cannot centralize all four while retaining `s_11`.  This no-go has now been
strengthened to the correct commutant-valued condition on every rectangular
block between Boolean subset modules.  All 16 ordered block types have zero
phase image.  In the natural eight-point module, the only first jets that
extend through order two are the four chart-commutant matrices; this yields an
all-order no-go over every `F_2[epsilon]/(epsilon^N)`.  Full proofs and exact
certificates:
`notes/FALSE_ATLAS_DUAL_NUMBER_CENTRAL_QUOTIENT.md` and
`notes/FALSE_ATLAS_BOOLEAN_DUAL_NO_GO.md`.

The exact next target has two logically distinct forms.  On the negative
side, enlarge the perfect-overlap/full-Leavitt relation package until one can
decide whether `s_11` dies in `R/[P,R]`.  On the positive side, construct a
different full-chart finite or tracial model in which all four survivors are
central while `s_11` remains nontrivial, and then extend that control to
growing relation windows.  Quotienting the current finite image cannot work:
inside it, `[rho(s_30),rho(g)]=rho(s_11)` for a chart generator `g`.
The repository contains no completed non-Boolean modular construction beyond
this boundary.  Raising the dual-number order in the natural module is now
closed, not live.  Any surviving construction must also avoid prefix
replication, which kills the central class homologically.

The modular first-order obstruction is now universal, rather than a screen
of selected modules.  For each aligned word `w`, its square-zero derivative
is one element `d_w` of `F_2[A_8]`, acting by conjugation on the endomorphism
space of any module.  An exact 552-step left-ideal certificate proves

```text
d_11 in sum_z F_2[A_8] d_z
        + sum_(s in {11,30,44,55}, g in S)
            F_2[A_8] (g+1)d_s.
```

Therefore the 24 certified zeros and commutant-valued centrality of all four
survivors kill the `s_11` jet on every `F_2[A_8]` module, including arbitrary
indecomposables, direct sums, multiplicities, and off-diagonal couplings.
Searching for a new module in any characteristic at the inner square-zero
alignment is closed by the all-fields signed group-algebra theorem above. A
surviving construction must change deformation order/geometry, order-zero
holonomy, or the common-module setup.
Full theorem and replayable certificate:
`notes/FALSE_ATLAS_UNIVERSAL_MODULAR_FIRST_ORDER_NO_GO.md`.

### 2026-08-12: compact and weakly compact anchors are impossible

For an arbitrary subgroup `Gamma<G` and a compressor
`t Gamma t^(-1)<=Gamma`, every finite-dimensional `G`-representation has

```text
rho(t)Fix_Gamma=Fix_Gamma.
```

More strongly, every `Gamma`-intertwiner between two finite-dimensional
`G`-representations automatically intertwines every inverse predecessor
`h=t^(-1)gamma t`.  Passing blockwise to an almost-periodic representation
gives the exact bicommutant inclusion

```text
pi(Gamma)' subset pi(h)'.
```

Thus the exclusion is fully noncommutative: compact multiplicity spaces do
not contain the one-wall witness either.

Hence every inverse predecessor `h=t^(-1)gamma t` fixes `Fix_Gamma`
pointwise.  Direct sums prove that in every compact pmp action of `G`, every
`Gamma`-invariant measurable function is already `h`-invariant.  If `G`
has property `(T)`, Ioana's invariant-vector argument upgrades every
ergodic weakly compact action to a compact one, so the exclusion applies to
all weakly compact actions as well.

Therefore the new relative-bicommutant endpoint cannot be realized by a
profinite, compact, weakly compact, or compact-OE action.  A classical
solution must be a CE but genuinely non-weakly-compact action; alternatively
the witness must be noncommutative.  Full proof:
`FALSE_COMPACT_ACTION_RELATIVE_ANCHOR_NO_GO.md`.

### 2026-08-12: paired HS models collapse to one relative commutant

For `D=G *_Gamma G` and `w=i_2(h)i_1(h)^(-1)`, the paired tracial endpoint
has an exact one-representation form.  A CE representation of `D` retaining
`w` exists if and only if, after at most one `2 by 2` amplification, there
are a CE finite algebra `M`, a homomorphism `pi:G->U(M)`, and a unitary

```text
v in pi(Gamma)' intersect M
```

with `[v,pi(h)]!=1`.  Equivalently,

```text
pi(h) notin (pi(Gamma)' intersect M)' intersect M.
```

Conjugating `pi` by `v` gives the two vertex maps; conversely the flip of
the block sum of any two compatible vertex maps gives `v`.  Since the fixed
double word lies in the full sofic radical, one such relative-bicommutant
escape proves FALSE.

At matrix level this is exactly one HS-asymptotic homomorphism
`pi_n:G->U(d_n)` and one unitary `v_n` with

```text
||[v_n,pi_n(gamma)]-1||_2->0       (gamma in Gamma),
liminf ||[v_n,pi_n(h)]-1||_2>0.
```

Conversely any paired construction becomes this one-map form by block sum
and the flip.  This removes all formally independent second-vertex fiber
variables from the live finite problem.

The classical specialization is equally sharp: a CE pmp action of `G` with
a `Gamma`-invariant function moved by `h` suffices.  A generalized Bernoulli
action over `G/K` supplies the function when `Gamma<=K` and `h notin K`.
This explains why the new amenable conjugacy stabilizer does not itself
finish the proof: `C_G(h)` is amenable and therefore cannot contain the
nonamenable Kazhdan group `Gamma`.  It supplies transport charts but no
`Gamma`-fixed anchor.  Full proof:
`FALSE_RELATIVE_BICOMMUTANT_ENDPOINT.md`.

### 2026-08-12: the framed FALSE endpoint is paired HS, not MF permanence

The three-tag construction gives a radical-marked element `h` whose full
conjugacy centralizer in the vertex group is amenable.  Hence the actual
conjugacy action `G curvearrowright G/C_G(h)` has finite root-dependent
sofic Schreier charts.  An irrational coadjoint character simultaneously
assigns the phases of all conjugate square-zero labels, so the integral
additive and covariance relations are exact before finite truncation.

The remaining theorem is now precisely a paired tracial extension: construct
HS-asymptotic maps `phi_(0,n),phi_(1,n):G->U(k_n)` which agree on every fixed
element of `Gamma` but retain positive normalized HS displacement between
the two images of `h`.  Their tracial-ultraproduct limits then define
`D=G *_Gamma G -> U_omega`; its image is hyperlinear, retains the nontrivial
word in `Rad_sof(D)`, and is therefore nonsofic.  Faithfulness is unnecessary.

This direct HS endpoint corrects an important possible misstatement:
Shulman's amalgamated-MF theorem is an operator-norm conclusion and does
**not** imply hyperlinearity.  Operator-norm visibility may occupy vanishing
normalized rank.  Full construction and corrected endpoint:
`FALSE_FULLY_FRAMED_AMENABLE_CONJUGACY_ORBIT.md`; exact character model:
`FALSE_AMENABLE_COADJOINT_FRAME_CHARACTER.md`.

### 2026-08-12: exact level-169 packet saturation and parity repair

The twelve-cycle level-`169` packet has exact projected lattice index two.
An unused cycle gives a one-row replacement of odd index seven, and signed
determinant linearity turns it into the explicit unimodular correction

```text
c_new=c_15-3c_3.
```

The repaired packet is a `Z`-basis of `Q_169`; its maximum coefficient is
`6`, maximum squared row norm is `824`, and maximum absolute Gram row sum is
`1018`.  More generally, an index-two packet plus one odd-index replacement
is repaired by `x +/- ((m-1)/2)c_j`.

Because the ambient cycle kernel is primitive, every coordinate functional
of this `Q_169` basis extends to an integral ambient covector annihilating
the boundaries.  Hence qualitative integral dual lifting is solved in all
twelve directions.  The live TRUE gate is now quantitative: produce these
extensions with a family-uniform synthesis norm.  A generic HNF extension
can be astronomically large and is not the desired certificate.  Full proof:
`TRUE_SQUARE_LEVEL_INTEGRAL_PACKET_INDICES.md`.

The extension fiber is now identified exactly as
`Sat(Row_Z(d_2^T))=Row_Q(d_2^T) intersect Z^N`, not merely the raw
coboundary row lattice.  The quotient between them is the `Ext^1` group
coming from torsion in `coker(d_2)`.  Thus the first greedy reducer operated
in a finite-index sublattice and its huge output is inconclusive.  The next
quantitative calculation must reduce in the saturated annihilator.

This quotient is canonically `Ext^1(H_1,Z)`.  At level `169`, the rank of
`d_2` is full modulo `2,3,5,7` and drops by one modulo `13`.  The unique
missing `13`-direction has now been extracted explicitly: it has support
`1533`, squared norm `2103`, maximum coefficient `3`, and adjoining it
restores full rank modulo `13`.  Hence the entire visible `13`-primary
saturation defect is one certified row.

Across the five exact square charts, the complete groups are now

```text
Tor H_1(X_9;Z)=0,
Tor H_1(X_25;Z)=C_25,
Tor H_1(X_49;Z)=C_49,
Tor H_1(X_121;Z)=C_831875=C_(5^4 11^3),
Tor H_1(X_169;Z)=C_13.
```

Exact saturation indices give the orders, and one-dimensional modular rank
drops at every divisor force cyclicity.  These groups are precisely the
finite arithmetic directions missing from raw-row dual reduction.  The
level-`9` lattice is already saturated, while levels `25` and `49` have the
simple groups `C_25` and `C_49`.  The unexpected `5^4` at level `11^2` and
the order-`13` rather than order-`169` group at level `13^2` rule out a
level-prime-only formula; the family theorem must include the fixed
stabilizer primes.  Full proof:
`TRUE_SQUARE_LEVEL_H1_TORSION.md`.

### 2026-08-12: determinant-one primal section at level 121

Boundary reduction of the full exact square-level packets improves the
finite bounds to maximum squared norms `95` at level `121` and `133` at
level `169`.  More decisively, exact pairing with a basis of `Q_121^#`
shows that the seven projected level-`121` cycles have determinant one and
therefore form a `Z`-basis of `Q_121`.  After transporting the short primal
LLL basis and reducing by boundaries, there is a full integral primal
projection section with coefficients only `0,+-1` and operator norm
`14.3173701531...`.  This solves primal saturation/absolute realization in
that chart.  It is not the dual carry section of the harmonic lift sequence.
The family target is now a uniform determinant-one packet and uniform
primal section bound, followed separately by uniform control of the dual
carry extension.  Full certificate:
`TRUE_SQUARE_LEVEL_BOUNDARY_REDUCED_SECTIONS.md`.

### 2026-08-12: untwisted even-edge reduction

`FALSE_FREE_HALF_CIRCLE_SPATIALIZER.md` proves that the one-vertex twisted
target embeds trace preservingly in the ordinary symmetric reduced amalgam
over the even edge:

```text
N_one
 subset pL(J) *_pL(K_0) pL(J)
 isomorphic pL(J *_K_0 J).
```

The spatializer is `sgn(Im(q_1q_2))`; the product `q_1q_2` is a Haar
unitary commuting with the even edge and inverted by the first odd
involution. This removes the parity twist from the remaining target. The
right-hand group is already weak MF by Shulman's symmetric-double theorem.
The live gate is still tracial: prove CE of its canonical reduced trace (or
an MF trace on the displayed subalgebra retaining the scalar
anticommutation). Full-C-star MF alone does not supply that trace.

### 2026-08-12: level 121 has an exact short rank-two cellular packet

The modular fundamental-circuit screen at level `121` isolates the same two
small homology-bearing supports in characteristics `101`, `1009`, and
`10007`.  Exact integer lifting gives primitive cycles `c_1,c_2` with

```text
|supp(c_1)|=16, ||c_1||^2=40,
|supp(c_2)|=17, ||c_2||^2=35,
Gram(c_1,c_2)=[[40,20],[20,35]],
```

and coefficients only `+-1,+-2`.  Their quotient signatures are independent
modulo all three primes.  Since the boundary rank is exactly `625`, modular
rank `627` of `[d_3;c_1;c_2]` proves that the two classes are independent in
rational `H_2`.

This is an explicit rank-two primal packet in actual cellular coordinates,
not just a reduced harmonic Gram basis.  Its rank matches the independently
known cuspidal quotient dimension at `121`, but the absolute-to-relative map
has not yet identified the packet as cuspidal.  The remaining five quotient
directions are dense in this particular pivot basis, matching the boundary
kernel split only heuristically.  Full certificate:
`TRUE_N121_SHORT_CIRCUIT_PACKET.md`.

### 2026-08-12: fundamental-circuit height is an exact packet certificate

For an integral closing matrix `beta:Z^I->E`, choose pivot columns `F` and
write every nonpivot column in its primitive integral dependence

```text
a_e beta(e)=sum_f b_(e,f) beta(f).
```

The vectors

```text
c_e=a_e e-sum_f b_(e,f)f
```

are independent integral circuits spanning `ker(beta_R)`.  If their norms
are at most `A` and the integral comparison from closed symbols to absolute
cycles has norm at most `C`, their harmonic projections span the primal
lattice with norm at most `CA`.  Hence

```text
lambda_1(Q_X^#)>=1/(CA).
```

The integral defect is also exact: the quotient of the full kernel by the
fundamental-circuit lattice is killed by `lcm_e(a_e)`; when every `a_e=1`,
the circuits are a `Z`-basis.  This converts the Ash--Rudolph closing gap
into a finite proposed-certificate problem: find projective pivot sets with
uniformly bounded primitive dependence height, plus a bounded absolute
realization.  The four supplied stability/expansion papers do not provide
this integral kernel statement.  Full proof and source audit:
`TRUE_FUNDAMENTAL_CIRCUIT_PACKET_CERTIFICATE.md`.

### 2026-08-12: paired carry collapses to cycle carry under the word frame

For a regular cover with `N` marked-word coordinates, let `Q delta_x=q_x`
be the synthesis of the canonical minimum real word fillings.  If
`||Q||<=C`, every discriminant class satisfies

```text
mu_w(c)<=2 pi C rho_L(gamma(c))/sqrt(N).
```

If `d` realizes the exact paired carry energy of `c`, then

```text
rho_K(d)<=delta(c),
mu_w(d)>=mu_w(c)-2 pi C delta(c)/sqrt(N).
```

Hence, over covers of one fixed presentation, a microscopic exact-carry,
macroscopic-word sequence exists exactly when a microscopic-cycle,
macroscopic-word sequence exists.  The range-side term of the paired
infimal convolution creates no additional FALSE endpoint after the Kazhdan
marked frame is bounded.

For a canonical filling class `c_y`,

```text
mu_w(kc_y)<=2 pi C^2 |k|/sqrt(N).
```

Thus marked cyclic amplification requires square-root-scale multiplier and
order, sharply strengthening the earlier qualitative order escape.  Full
proof: `FALSE_BOUNDED_FRAME_PAIRED_CARRY_COLLAPSE.md`.

### 2026-08-12: bounded frames close canonical binary phase incidence

Let `Q delta_x=q_x` and `R delta_j=r_j` be finite Hilbert synthesis
families with norms at most `C,D`.  If all pairings
`<q_x,r_j> mod Z` have order dividing `M`, Bessel's inequality gives

```text
max_x |{j:<q_x,r_j> notin Z}|<=M^2 C^2D^2,
max_j |{x:<q_x,r_j> notin Z}|<=M^2 C^2D^2.
```

For canonical filling translates, `R` is a restriction of `Q`, so the
bound is `M^2C^4`.  The Kazhdan orbit-frame theorem supplies a uniform `C`
throughout the bounded-intermediate-real branch.  Consequently every
canonical order-two marked incidence row has weight at most `4C^4`, and the
binary Bernoulli condition `a_n/b_n->0` is impossible.  Any bounded-order
correlated generator family satisfying that criterion must have unbounded
real synthesis norm.

If the canonical code is totally isotropic, `Q^*Q` is integral; its bounded
operator norm then forces at most `C^4` nonzero autocorrelations per deck
row.  This reduces the last isotropic branch to a sparse integral
spectral-factor problem.  Gram integrality alone does not give an integral
decoder, as an exact three-coordinate counterexample shows.  Full proof:
`FALSE_BOUNDED_FRAME_PHASE_INCIDENCE_NO_GO.md`.

### 2026-08-12: finite-index covers do not revive the central radical

For the explicit Kun--Thom double

```text
D=G *_Gamma G,   D_N=G *_N G,   R=ker(D->D_N),
```

the earlier calculation gave only `R/[D,R]=0`.  The possible finite-cover
escape is now closed: for every finite-index `L<=D`,

```text
Rad_sof(L)=R_fin(L)=R=[L,R].
```

Equivalently, if

```text
A=ker(Z[D_N/Gamma] -> Z[D_N/N]),
```

then `A_H=0` for every finite-index `H<=D_N`.  After replacing `H` by its
normal core, Mackey--Shapiro expresses `A_H` between stabilizer
abelianizations and orbit modules.  Infranormality makes `Gamma` and `N`
indistinguishable in every finite image of `D_N`, so the orbit map is a
bijection.  The split form `D_N=N semidirect(Q*Q)` and property `(T)` of
`N` produce a finite quotient retaining each stabilizer abelianization;
finite-image indistinguishability then makes every stabilizer map onto.
Exactness gives `A_H=0`.

Thus no congruence cover, nonnormal finite-index subgroup, or new
presentation of such a cover can turn the banked radical into a nonzero
ordinary central class.  The surviving FALSE mechanism must remain
noncentral and genuinely nonliftable.  Full proof:
`FALSE_FINITE_INDEX_RADICAL_COINVARIANT_NO_GO.md`.

### 2026-08-12: property (T) kills the inverse-root rate escape

Let `Gamma=<S>` have Kazhdan constant `kappa`, let `W` be a `Gamma`-module,
and let `(rho_i,Phi_i)` be two exact finite-dimensional covariant unitary
realizations of `Gamma semidirect W`. If `T` has base-intertwining defect
`eta` on `S` and seed-intertwining defect `epsilon` on `z in W`, then for

```text
w=sum_nu n_nu g_nu z,     C=sum_nu |n_nu|,
```

one has the word-length-free bound

```text
||Phi_0(w)T-T Phi_1(w)||_2
 <= C epsilon + 2(C+1) eta/kappa.
```

The proof projects `T`, in the Hilbert--Schmidt bimodule, onto the exact
base-intertwiner space before transporting the seed. Exact covariance then
makes every translate cost the same; no length of `g_nu` appears.

For the paired Frobenius labels the four-orbit identity gives `C<=2r`, so
the inverse fold is bounded by

```text
2r epsilon + (4r+2) eta/kappa.
```

This closes the apparent escape in which the positive word length of
`x_1^(-1)` grows while `lambda_n^- eta_n` remains macroscopic. That escape
cannot occur with exact Kazhdan base representations and exact tangent
covariance. A successful FALSE model must put genuine normalized-HS
nonliftability into the base action or covariance itself. Full proof:
`FALSE_KAZHDAN_CYCLIC_SEED_PROPAGATION_NO_GO.md`.

### 2026-08-12: the scattering graph is a critical-value lattice gate

The square-level graph operator is now split packetwise into its exact
arithmetic factors. For the balanced `(2,1)` Kostant representative of the
trivial `GL_3` coefficient system, the inducing weights are

```text
mu=(0,-1),   mu'=1,
```

so the Harder--Raghuram formula gives `m_0=1`. Hence on each weight-three
Hecke packet

```text
C_f = alpha_f R_f,
alpha_f = u_f c_infinity L^coh(f x chi,1)
          / (Omega_f^epsilon L^coh(f x chi,2)),
```

where `R_f` is the normalized local intertwiner and `u_f` is the arithmetic
comparison factor. Harder--Raghuram prove the critical ratio algebraic but,
over a field, do not control the integral valuations of `u_f`. Every
unramified finite factor sends the normalized spherical vector to its
counterpart; only the level-`p` local factor varies.

An exact DVR calculation shows that, wherever `R_f` is an integral lattice
isomorphism, the two projection indices of the primitive graph have total
length

```text
rank(V_f) * |v_q(alpha_f)|.
```

More intrinsically, if the full scattering map has local Smith exponents
`a_1,...,a_r`, the two primitive-graph projection lengths sum exactly to
`sum_i |a_i|`.  If the normalized local operator has exponents `b_i`, then
`a_i=v_q(alpha_f)+b_i`; scalar and conductor valuations may cancel, so only
the full Smith height is normalization-independent.

Thus swapping the two maximal faces only exchanges numerator and
denominator; it cannot remove the height of the full scattering slope. The
square-level integral gate now has four separate inputs: critical-value
plus comparison-factor valuations, the ramified `p`-local conductor,
Eisenstein saturation torsion, and automorphic-to-cellular metric
comparison. Full proof:
`TRUE_SQUARE_LEVEL_SCATTERING_LVALUE_GATE.md`.

### 2026-08-12: bounded central coefficients are one global vector

For a finite presentation \(P=F/N\), put

\[
\widetilde R=\bigcap_{N\leq L\lhd_{\rm fi}F}L,
\qquad
J=\bigcap_{N\leq L\lhd_{\rm fi}F}[F,L].
\]

For a finite-residual word \(w\), the shortest relator coefficient vectors
in the canonical modules \(L/[F,L]\) are uniformly bounded if and only if
one integral vector represents \(w\) in every module. Equivalently,

\[
\sup_L\delta_L(w)<\infty\quad\Longleftrightarrow\quad W\in NJ.
\]

The intersection has an exact structural meaning. For the central envelope

\[
E=F/[F,\widetilde R],
\qquad
Z=\widetilde R/[F,\widetilde R],
\]

one has

\[
J/[F,\widetilde R]=R_{\rm fin}(E).
\]

Hence canonical central amplification is governed by the single obstruction

\[
\Omega=
Z/\bigl(N[F,\widetilde R]/[F,\widetilde R]+R_{\rm fin}(E)\bigr).
\]

A nonzero sofic-radical class in \(\Omega\) is a complete FALSE
certificate. If \(E\) is residually finite, \(\Omega\) is exactly
\(R_{\rm fin}(P)/[P,R_{\rm fin}(P)]\). The infranormal
relative-\(H_1\) theorem then shows that every element of a Kazhdan
Kun--Thom double kernel has zero class in \(\Omega\); when the quotient
double is residually finite, \(\Omega=0\) outright. Thus changing its ring
or compressor cannot revive the marked central route. Full proof:
FALSE_DIRECTED_COEFFICIENT_COMPACTNESS.md.

### 2026-08-12: the square-level Eisenstein kernel is one scattering graph

The square-level dimension pattern is now proved for every odd prime:

```text
dim H_Eis^2(Gamma_0(p^2,3))
 = dim S_3(Gamma_1(p))
 = dim S_2(Gamma_0(p^2))-dim S_2(Gamma_0(p)).
```

For `p>=5` the common value is `(p-1)(p-5)/12`; at `p=3` it is zero.
Lee--Schwermer's exact degree-two boundary module has a twisted cusp term
and two sign terms for each maximal-parabolic type. Taking
`Gamma_0(p^2)`-invariants and using Ash--Yasaki's face stabilizers kills all
sign terms and all faces except the middle `d=p` face of each type. The
boundary is therefore two copies of `S_3(Gamma_1(p))`, and the Eisenstein
Lagrangian is exactly the graph of the constant-term intertwiner
`C_p^*(0)` between them.

This replaces arbitrary square-level boundary packets by one explicit
weight-three modular-symbol lattice and one scattering graph. The remaining
family gate is integral: bound modular-symbol packets and the denominators
and metric distortion of `C_p^*(0)`. Full proof:
`TRUE_SQUARE_LEVEL_EISENSTEIN_GRAPH.md`.

### 2026-08-12: the boundary kernel is dual degree-two Eisenstein cohomology

For every oriented compact five-manifold, the image

```text
E^2=im(H^2(M;Q)->H^2(partial M;Q))
```

is Lagrangian for the four-dimensional boundary intersection pairing.
Consequently `H^2(partial M)/E^2` is canonically `E^2*`. In the Borel--Serre
pair sequence this sharpens the previous split to

```text
0 -> (H_Eis^2)^* -> H_2(Gamma;Q) -> H_cusp^3(Gamma;Q) -> 0.
```

Thus the five level-`121` boundary directions are exactly the dual of a
rank-five degree-two Eisenstein image. The family target is no longer an
unspecified boundary packet theorem: it is bounded Eisenstein restriction
packets plus bounded cuspidal closing.

Integrally, if `E_sat` is the primitive saturation of the boundary image in
the unimodular boundary lattice `L`, then

```text
0 -> E_sat/E -> L/E -> E_sat^* -> 0.
```

The finite group `E_sat/E` is precisely the extra denominator/gluing layer.
This puts the boundary problem directly into the paired-discriminant
framework. Full proof: `TRUE_BOUNDARY_KERNEL_IS_EISENSTEIN_DUAL.md`.

The first discriminating square-level check also succeeds: level `49` has
exact homology `(1,0,1,9)`, no cuspidal degree-three contribution, and hence
a rank-one Eisenstein kernel. Together with levels `9,25,121`, this matches

```text
dim H_Eis^2(Gamma_0(p^2))
  = dim S_2(Gamma_0(p^2))-dim S_2(Gamma_0(p))
```

for `p=3,5,7,11`. The formula is now proved for every odd prime by the
preceding Lee--Schwermer/Ash--Yasaki descent.

### 2026-08-12: absolute H2 has an interior quotient and a boundary kernel

The Borel--Serre pair sequence and Lee--Schwermer boundary theorem give the
rational short exact sequence

```text
0 -> coker(H^2(Ybar)->H^2(partial Ybar))
  -> H_2(Gamma;Q)
  -> H_cusp^3(Gamma;Q)
  -> 0.
```

This changes the packet strategy at level `121`. The exact projective
computation gives absolute `H_2` dimension seven, while Ash--Yasaki compute
cuspidal dimension two. Therefore the seven harmonic directions split as a
five-dimensional boundary kernel and a two-dimensional cuspidal quotient.
Relative unimodular symbols cannot see the five kernel directions.

The corrected family theorem has three independent gates: bounded cuspidal
closing in modular symbols, bounded Borel--Serre boundary packets, and
bounded integral/metric gluing of the two filtrands. The immediate exact
experiment is to apply the absolute-to-relative map to the seven level-`121`
primal packets and isolate the predicted `5 -> 7 -> 2` decomposition. Full
proof: `TRUE_ABSOLUTE_H2_INTERIOR_BOUNDARY_SPLIT.md`.

### 2026-08-11: Ash--Rudolph supplies templates but leaves the closing kernel

The unimodular modular-symbol theorem gives canonical level-independent local
templates: every top-degree modular symbol is an integral sum of determinant-
one symbols.  It does not yet prove the primal packet theorem.  Absolute
cycles form the kernel of the boundary-at-infinity map inside the relative
modular-symbol module.  Even an integral `0,+-1` boundary matrix with two
entries per row can have kernel `Z(1,...,1)` and first minimum `sqrt(m)`.

Thus the exact modular-symbol target is a bounded integral closing theorem:
the kernel of the signed projective boundary incidence must be real-spanned
by uniformly bounded integral combinations of unimodular symbols.  This
identifies the canonical packet candidates and the precise missing family
input without claiming that local generation implies global closing.  Full
audit: `TRUE_ASH_RUDOLPH_PACKET_SCOPE_AUDIT.md`.

### 2026-08-11: exact primal-packet family screen isolates level 53

Exact Gram--LLL has now been run on the primal harmonic lattices at levels
`53,61,73,79,89,97,121`.  The ranks are `2,2,0,2,2,0,7`.  At every
positive-rank level except `53`, a determinant-one packet basis has maximum
absolute Gram row sum strictly below the chart's spherical threshold.  The
values are `8.1805<28`, `8.0253<28`, `1.7218<12`, and `8.7642<12` at
`61,79,89,121`, respectively.  Hence the entire packet synthesis operator,
not just each basis vector, is chart-safe.  At `121`, all seven genuinely new
directions satisfy this stronger certificate.

Level `53` is the unique tested failure: its maximum squared packet norm is
`14.0242>12` and maximum Gram row sum is `14.0825>12`.  This is a failure of
the sufficient packet screen, not a negative result, and matches the already
known exceptional paired-discriminant chart.  The theorem-shaped target is
now a uniform bounded projected-packet construction for generic levels plus
finite paired-discriminant treatment of exceptional levels.  Ambient
integral lift norms remain a separate numerator gate.  Full proof and exact
certificates: `TRUE_PROJECTIVE_PRIMAL_PACKET_FAMILY_SCREEN.md`.

### 2026-08-11: the local positive-commutant gate is exact character matching

The paired-Fourier FALSE endpoint no longer contains a local dense-unitary
optimization.  For a finite abelian tangent module `A`, positive subgroup
`P`, representation `pi`, and marked class `m`, the maximum displacement of
`pi(m)` by a unitary commuting with `pi(P)` is an exact assignment problem
inside the fibers of `A^ -> P^`.  For the regular representation it depends
only on `r=ord_(A/P)(m+P)`: `0` for `r=1`, `4` for even `r`, and
`2+2 cos(pi/r)` for odd `r>1`.

Hence every surviving marked quotient class gives squared normalized-HS
energy at least three, attained by a Pauli character multiplier.  The
remaining globalization variables are discrete annihilator characters
subject to external relative-cocycle and stabilizer congruences.  Future
compute should build that sparse modular CSP and return a feasible exact
assignment or a dual inconsistency certificate; it should not optimize
dense unitaries.  Honest finite Laurent quotients in which the positive
image already contains the inverse have `r=1` and are exactly sterile.  Full
proof: `FALSE_POSITIVE_COMMUTANT_CHARACTER_MATCHING.md`.

This reduction is robust.  If `epsilon` is the RMS commutator of an
arbitrary unitary with the whole positive subgroup, conditional expectation
and polar correction produce an exact positive-commutant unitary within
`sqrt(2) epsilon`.  Its marked displacement changes by at most
`2 sqrt(2) epsilon`.  Hence diffuse approximate walls cannot beat the exact
character assignment asymptotically, and an absorbed marked class has
marked norm at most `2 sqrt(2) epsilon`.

For control only on a finite generating window `S`, the exact loss is the
inverse square root of

`eta(S)=min_(1!=nu in P^) sum_(s in S)|nu(s)-1|^2`.

This is the positive dual Cayley spectral gap.  The marked norm is at most
the exact assignment optimum plus `4 Def_S/sqrt(eta(S))`.  Therefore the
only local finite-window escape is a surviving marked quotient class
together with `eta(S)->0`.  On a cyclic clock of order `M`,
`eta(S)=4 sin^2(pi/M)`, recovering exactly the high-order phase mechanism.
The global FALSE problem is now to transport that minimizing clock character
through the relative cocycle/stabilizer system without incurring positive
mass elsewhere.

Combining the exact assignment and finite-window estimates gives the local
branch-cut/soft-clock dichotomy.  If the marked norm has a fixed lower bound
while the positive commutator defect tends to zero, then either the marked
class remains outside the positive spectral restriction fibers, or the
positive character gap tends to zero.  Quantitatively,

`D<=sqrt(E_exact)+4 Def_S/sqrt(eta(S))`.

For a regular block the first branch is exactly `m notin P` and has energy
at least three.  If `m in P`, then `E_exact=0` and a marked lower bound `c`
forces `eta(S)<=16 Def_S^2/c^2`.  Thus every local escape is now classified
as either a genuine growing branch cut or a high-order clock.  The remaining
question is exclusively whether one of these arithmetic objects satisfies
the nonliftable external cocycle/stabilizer equations.

## 1. Finite-action character transfer  [ACTIVE]

Fix a finite multiplication table and let `F_T` be the free group on its
labels.  The table defects are words `r=x_q⁻¹x_sx_t`, and unequal-pair
witnesses are words `w=x_t⁻¹x_s`.  A permutation table is exactly a finite
`F_T`-action `ρ`, with

* `d_Ham(σ_sσ_t,σ_q) = 1 - χ_ρ(r)`;
* `d_Ham(σ_s,σ_t) = 1 - χ_ρ(w)`,

where `χ_ρ(g)` is the fixed-point fraction of `ρ(g)`.  These identities are
kernel-checked in `Sofic/FiniteActionCharacter`.

Globally, for `Γ=F_k/N`, hyperlinearity says that the normal `0/1` character
`1_N` is a pointwise limit of normalized finite-dimensional unitary
characters; soficity says that it is a pointwise limit of finite-action
fixed-point characters.  Thus the live theorem is the normal-IRS transfer

`co-hyperlinear δ_N  =>  co-sofic δ_N`.

The normality and `0/1` limit are essential.  Nonnegative unitary characters
need not be finite-action characters (the `C₄` inequality in `notes/NOTEPAD.md` is
an explicit obstruction), and no modulus can be uniform over changing word
tables.  Pointwise rounding `U(d) -> Sym(X)` is also impossible: zero defect
would make it a homomorphism, and every homomorphism from divisible `U(d)` to
a finite group is trivial.  The conversion must therefore be table-dependent
and may choose its input tolerance after the finite word table is fixed.

Next: exploit the asymptotic normal `0/1` limit in the dual finite-action
inequality `(NIR7)`.  A successful proof must rule out every finite separator
of `1_N` from the closed convex set of finite-action characters; generic
unitary-character density, full metric-sofic approximation of `U(d)`, and
Fell density of finite-image representations are all strictly too weak or too
strong in the wrong direction.

The Fournier-Facio--Willett very-flexible theorem now sharpens the last item:
for the free source it does produce finite-quotient representations whose
corners approximate the whole unitary table (`(VFC1)-(VFC5)`).  It gives no
ambient-dimension bound, however, and pointwise almost-invariance of the
corner does not control the full finite-quotient twirl (`(VFC6)-(VFC9)`).
Even centralizing that corner would yield a finite-image unitary character,
not yet a finite-action character.  Treat trace centralization and the
permutation-character conversion as two separate gates.

Property MD of the free source does not repair the second gate.  Finite
actions are dense only in the weak action topology, where fixed-point measure
is discontinuous: the order-`m` rotation of the circle has no fixed points
but converges weakly to the trivial action (`(MDG1)-(MDG4)`).  Thus pulling
back a free quotient action and invoking MD loses exactly the normal-Dirac
statistics required for soficity.

Exact doubled form (proved in `notes/NOTEPAD.md`, `(DCT1)-(DCT9)`): for
`H_N={(a,b) in F x F : aN=bN}`, hyperlinearity is precisely approximation of
`1_(H_N)` by the canonical maximally-entangled coefficients of
`pi(a) tensor overline(pi(b))`; soficity is precisely approximation by the
canonical diagonal-set coefficients of `P_a tensor P_b` from a common finite
`F`-set.  Thus the missing implication is a restricted diagonal rounding
theorem for normal fiber-product indicators.  General synchronous-correlation
results do not supply it: maximally-entangled quantum correlations need not be
classical, while their known density theorem stays inside the quantum cone.

Source audit `(SA1)-(SA6)` now pins this to Manzoor's exact closure gap:
`closure(T_IRS intersect T_fd)` versus
`T_IRS intersect closure(T_fd)` at the normal Dirac trace.  The quantitative
theorem of Burton--Chaudkhari--Juschenko--Muliarchyk proves the transfer for
amenable quotients, with doubled coefficient error at most `2 sqrt(epsilon)`
after matrix rounding.  Subgroup tests capture all finite separators but do
not make the separating IRS normal Dirac, and HS-stability results stop at
exact matrices rather than permutation actions.

The positive-loss obstruction now has a one-witness transitive normal form;
see `TRUE_ONE_WITNESS_TRANSITIVE_LOSS.md`.  If TRUE fails, there are fixed
`R subset N`, one `w outside N`, nonnegative weights, and `epsilon>0` such
that every finite-index subgroup `H<=F` has weighted loss at least `epsilon`
after averaging membership over the conjugates represented by `F/H`, while
finite-dimensional characters have loss tending to zero.  Orbit
decomposition proves that testing arbitrary finite actions gives exactly the
same infimum as testing the quasiregular actions `F/H`.  Thus disjoint unions
and multiple witnesses are no longer part of the gate; the missing theorem
is the normal-indicator rounding from unitary characters to one finite
quotient/subgroup pair `(Q,J)` with small averaged Boolean loss.

Cartesian powers sharpen this further to a linear, unweighted radical
inequality; see `TRUE_LINEAR_SOFIC_RADICAL_INEQUALITY.md`.  For the finite
presentation `P=<S|R>`, one has `w in Rad_sof(P)` if and only if some finite
`C` satisfies

`1-chi_rho(w) <= C sum_(r in R)(1-chi_rho(r))`

for every finite action `rho`; orbit decomposition again makes transitive
coset actions sufficient.  The amplification proof is exact: if no linear
constant existed, take actions with relator defect `o(d_rho(w))` and about
`1/d_rho(w)` Cartesian powers, producing vanishing relator defect but a
fixed positive motion of `w`, contrary to radical membership.  Thus a
counterexample requires finite-dimensional characters that maximally violate
one classical linear quasiregular-character inequality; arbitrary minimax
weights are not intrinsic to the gate.

Conjugate-double tensor powers give the exact parallel statement for the
hyperlinear radical; see `TRUE_RADICAL_DOMINATION_CONSTANTS.md`.  With
`q_chi(g)=1-|chi(g)|^2`, define the optimal ratios `C_perm` over finite
action characters and `C_fd` over all normalized finite-dimensional
characters.  Then

`C_perm<infinity iff w in Rad_sof(P)`,
`C_fd<infinity iff w in Rad_hyp(P)`, and `C_perm<=C_fd`.

Consequently TRUE is exactly the assertion that `C_perm<infinity` forces
`C_fd<infinity` for every finite presentation and word.  This is a sharper
target than full HS stability: only the one controlled word must collapse,
and the comparison constant may depend arbitrarily on the fixed presentation
and word.  A counterexample is exactly a finite classical domination
constant together with an infinite matrix-character domination constant.

The finite-dimensional singularity branch is now closed; see
`TRUE_FIXED_DIMENSIONAL_ARC_BOUNDARY.md`.  If `C_perm<infinity`, then the
restricted constant `C_fd(d)` is finite for every fixed matrix dimension
`d`.  Indeed an unbounded fixed-dimensional ratio has a semialgebraic bad
arc.  In the conjugate double, its relators vanish to higher power-series
order than its witness; truncation at the first witness jet produces an
exact homomorphism to a finitely generated complex linear group retaining
the radical word, impossible because that image is sofic.  Hence the only
remaining TRUE obstruction is uniformity in growing dimensions:

`C_fd(d)<infinity for every d`, but `sup_d C_fd(d)=infinity`.

This removes exact finite-stage searches, nonlinear fixed-dimensional
deformations, and singular projective solution strata from the live gate.

The matrix side can now be made irreducible as well; see
`TRUE_IRREDUCIBLE_DOMINATION_REDUCTION.md`.  With
`delta_sigma(g)=1-Re tr(sigma(g))`, conjugate-double decomposition and
trivial-block dilution give the exact equality

`C_fd=sup_(sigma irreducible) delta_sigma(w)/sum_R delta_sigma(r)`.

The restricted supremum over irreducibles of degree at most `D` is finite
for every `D`, again by jet truncation.  Even arbitrary total dimension and
multiplicity are harmless if all irreducible blocks have bounded degree.
Thus the live TRUE comparison is now between transitive finite permutation
representations and irreducible unitary representations whose degrees tend
to infinity; reducible mixtures and multiplicity growth are not part of the
gap.

The induced finite-image part of that growing-degree comparison is now
sharply controlled; see `TRUE_INDUCED_IDENTITY_GAP_DOMINATION.md`.  If
`sigma=Ind_H^F(tau)` and `tau` has finite image, its normalized character
defect is sandwiched against the moved fraction of the finite coset action
`F/ker(tau)`:

`min(1,eta(tau)) d_(F/ker(tau))(g) <= delta_sigma(g)`
`                                      <= 2 d_(F/ker(tau))(g)`,

where `eta(tau)` is the least normalized trace defect of a nonidentity
inducing block.  The classical radical inequality therefore transfers with
loss `2/min(1,eta(tau))`, independently of `[F:H]`.  In particular,
finite-image monomial irreducibles of bounded phase exponent, and more
generally induced finite-image blocks of bounded dimension and exponent,
cannot obstruct TRUE.  Any induced finite-image obstruction must have
identity gap tending to zero; growing coset degree alone is harmless.

The complementary unbounded-phase sector is now connected exactly to the
carry/discriminant program on every exact finite quotient chart; see
`TRUE_EXACT_COVER_MONOMIAL_DISCRIMINANT.md`.  Integral fillings of the
lifted radical loops give an integer factorization `B_(w,X)=Z_X A_X` from
relator holonomy to word holonomy.  The optimal additive monomial
domination constant is the marked torus Lipschitz ratio of this factor map,
and the optimal chordal/character constant is universally equivalent to its
square.  Its exact formula `(ECM31)` has the paired-discriminant lower
envelope as denominator and the canonical radical filling pairings as
numerator.  Hence bounded marked ratios rule out all phase orders on exact
charts.  The remaining monomial overlap is unbounded phase order on
nonexact permutation charts, plus possible growth of the marked ratios over
exact charts.

The nonexact monomial overlap has now been reduced further; see
`TRUE_NONEXACT_MONOMIAL_FIXED_PHASE_REDUCTION.md`.  For every arbitrary
finite monomial model, the witness character defect is exactly its moved
fraction plus its phase energy on fixed points.  The classical radical
inequality controls the moved fraction by the total relator defect, with no
permutation-stability hypothesis.  Hence monomial domination on all
nonexact charts is equivalent, up to universal chordal/geodesic constants,
to one partial-holonomy inequality: fixed-point phase energy of `w` must be
bounded by closed-relator phase energy plus the mass on which relator loops
do not close.  Any monomial obstruction therefore has asymptotically
negligible witness motion and macroscopic phase cancellation on fixed
points.  Conjugate doubling and trivial-block dilution show that this
affine monomial constant is exactly the usual phase-insensitive constant
defined by `1-|tr|^2`.  This does not solve the phase inequality, but removes
base motion as an independent source of the gap.

The level-`121` harmonic calculation has also been converted into a precise
family criterion; see `TRUE_HARMONIC_RIESZ_PACKET_CRITERION.md`.  If the
projected harmonic cycle lattices admit integral bases with uniformly bounded
Gram row sums, then `lambda_1(Q_X^#)` is uniformly bounded below, independent
of harmonic rank.  If the corresponding dual bases have bounded-overlap
integral ambient lifts, the harmonic exact sequences admit uniformly bounded
sections and every subthreshold class is repaired.  Thus the theorem-shaped
TRUE target is now a local packet construction with two Gram row-sum bounds;
finite exceptional levels can be absorbed.  The implication is proved, but
the uniform packet bases have not yet been constructed.

The supplied stability/expansion papers yield a separate dimension-free
synchronization theorem; see `TRUE_A3_METRIC_CONE_SYNCHRONIZATION.md`.  The
explicit nine-triangle cone in Dinur--Meshulam metricizes: for every
bi-invariant group length and every finite `L^r` exponent, an almost-flat
connection on `A_3(F_q)` is within factor `9` of a pure gauge.  This applies
uniformly to `U(d)` with normalized Hilbert--Schmidt length, `Sym(d)` with
normalized Hamming length, and circle phases.  Together with the Cartan-to-
monomial estimate it gives the explicit bound `9 delta+28 epsilon` for an
almost-flat, almost-monomial building connection.  For arbitrary words, a
uniform automorphism orbit of paths of length at most `L` changes its average
holonomy by at most `9 sqrt(3)L` times the curvature RMS.  However,
`TRUE_AUXILIARY_CONE_RADICAL_WITNESS_NO_GO.md` now closes this apparent escape
for the actual marked word.  The linear sofic-radical inequality controls the
fraction of paths whose endpoints move; every remaining path is closed and
is controlled by the cone.  In RMS Hilbert--Schmidt metric the explicit
combined bound is
`243 L^2 curvature^2+4 C_rad relator_motion`.  Hence a bounded-length,
bounded-congestion building encoding cannot retain the radical witness.
Positive-density endpoint motion would already violate the defining
finite-action inequality and amount to constructing the desired sofic
separation before applying the cone.  Becker--Lubotzky independently rules
out replacing the building by ordinary stability of an infinite
property-`(T)` presentation.  The auxiliary-cone lane is therefore closed;
the live universal gates remain direct character domination and
common-Cartan/fixed-phase control.

Full circle repair is a sufficient uniform bound for every marked radical
word: `(ECM24b)-(ECM24c)` give
`Lambda_(w,X)<=|w| C_circ(A_X)<=|w|Theta(A_X)/sigma_+(A_X)` and the
corresponding character constant is at most `pi^2/4` times its square.
Therefore the exact property-`(T)` Hodge gap plus a uniform integral-carry
bound closes arbitrary phase orders on all exact charts.  A marked ratio can
still remain bounded when full circle repair does not, so `(ECM31)` is the
sharper word-specific target.

The exact/nonexact chart transition now has a quantitative composition
theorem; see `TRUE_STABLE_BASE_CARRY_TRANSFER.md`.  Keep the original phase
labels while replacing the permutation part by an exact `P`-action.  If `h`
is the generator Hamming exactification cost, `E_R` is the relator HS defect,
and `C_circ` is the resulting exact-chart repair constant, then `(SBC17)`
gives

`||U(w)-1||_2 <= |w|sqrt(2h)`
` +(pi/2)|w|C_circ(E_R+sqrt(2h)L_R)`.

Hence sequencewise permutation exactification plus uniform carry repair
kills every monomial radical witness, with no bound on phase order.  In
particular, permutation stability of the presentation together with a
uniform exact-chart carry bound closes the entire monomial branch.  This
proves that base repair and phase repair have no hidden third compatibility
loss; what remains is to establish them for the relevant charts, and to
obtain a common Cartan/monomialization for arbitrary matrix characters.
The conclusion is unchanged under flexible exactification by adding or
removing `o(|X|)` points: extend both models to a common set with trivial
actions and phases, apply `(SBC17)`, and use the asymptotically unit dimension
ratio (`(SBC29a)-(SBC29b)`).

On the amplified FALSE lane, full base transfer reduces the modular
holonomy search to a fixed-rank dual norm; see
`FALSE_BASE_HOLONOMY_DUAL_NORM.md`.  For a fixed integral basis of the base
cycle lattice, center its `k` radical-transgression values modulo `q` into a
vector `c in Z^k`.  The optimal ratio
`sup_(v!=0) H_q(Hol(Jv))/||v||` has an exact finite shortest-representative
formula and is bounded above and below by fixed basis constants times
`||c||`.  Hence unbounded centered basis holonomy already supplies one fixed
primitive cycle to the amplified transfer-holonomy certificate and proves
FALSE.  Computationally, on full-transfer charts it is enough to solve the
`k` basis right-hand sides and watch one fixed-dimensional output vector;
searching over all base cycles is unnecessary.  Full transfer itself remains
a substantive unproved hypothesis for the candidate chart families.

The degree congruence gives that fixed-rank character an exact arithmetic
normal form; see `FALSE_FULL_TRANSFER_TORSION_NORMAL_FORM.md`.  If a regular
cover has degree `n`, modulus `q`, `g=gcd(n,q)`, and the whole base cycle
lattice transfers, then `e=q/g` divides the fixed Gram content of that
lattice.  Radical holonomy decomposes uniquely as
`Hol(Jv)=<v,z_0>+e psi(v) mod q` for a character
`psi:K_1->Z/gZ`.  Centered basis holonomy differs in norm from `e` times the
centered coordinate vector of `psi` by at most the fixed base-filling norm.
Since `e` ranges over finitely many divisors, the amplified FALSE condition
is exactly unbounded growth of this fixed-rank degree-torsion character.
Thus all full-transfer growth is confined to the common nonsemisimple part
of cover degree and modulus; the coprime sector is rigorously inert.

That torsion character itself is now identified with one paired integral
class; see `FALSE_TRANSFERRED_FILLING_PAIRING_FORMULA.md`.  Transfer an
integral filling of a lifted radical loop to the base and subtract a fixed
base filling.  Its class `kappa_(w,X) in K_1/S(K_X)` is independent of all
choices.  For every transferable `(v,q)`,
`Hol(Jv)=<v,z_0>+<v,kappa_(w,X)> mod q`; under full transfer the second term
is the mod-`q` Gram pairing on the transfer quotient.  In a fixed basis the
whole holonomy vector is exactly `f+Gm_X mod q`, and the degree-torsion
vector is `(G/e)m_X mod g`.  This removes the modular phase solve from the
marked numerator and identifies the remaining nonlinear obstruction with a
single relative filling class in a finite paired lattice quotient.
Bounded order of the marked class can already be decisive: if one fixed
primitive cycle detects it modulo unbounded transferable moduli, centered
holonomy is at least `q/E-O(1)` and amplification proves FALSE.  But bounded
exponent of the **whole** transfer quotient is the opposite, a TRUE no-go:
`E K_1<=S(K_X)` forces every transferable modulus for fixed `v` to divide
the constant `E gcd{<v,u>:u in K_1}`.  Hence finite-exponent `H_2(H,Z)`
rules out this modular-transfer route.  A bounded-order marked class can be
dangerous only inside ambient transfer quotients of growing exponent.

For the explicit stable Kun--Thom radical double, the marked class localizes
still further; see `FALSE_RADICAL_DOUBLE_AUGMENTATION_LOCALIZATION.md`.  The
kernel of `D=G *_Gamma G -> Q*Q` is the fundamental group of a tree of
perfect groups and is therefore perfect.  Consequently
`H_1(D,I_T)=H_1(Q*Q,I_T)` for every finite quotient module.  Although the
free-product Mayer--Vietoris sequence contains a large free Bass--Serre
overlap lattice, naturality from `H_2` forces the relative radical filling
class into `H_1(Q,I_T) directSum H_1(Q,I_T)` and gives it zero overlap
component.  Shapiro then expresses each vertex group by the exact sequence
`sum H_2(stabilizer)->H_2(Q)->H_1(Q,I_T)->sum H_1(stabilizer)->H_1(Q)`.
Thus the projective stabilizer-homology calculations locate the only live
arithmetic sector of the explicit radical-double numerator; free-product
rank growth cannot supply the obstruction.

The chain-level fixed-kernel argument closes that explicit tower
completely; see `FALSE_FIXED_KERNEL_COVER_NO_GO.md`.  If finite actions
factor through one quotient `H->L` and `w in [ker(pi),ker(pi)]`, fix a
commutator expression for `w` inside the kernel.  Every factor fixes every
cover vertex, so the lifted commutator chain cancels, and one fixed van
Kampen diagram gives fillings with `S z_(w,x)=z_0` on every cover.  Hence
`kappa_(w,X)=0` and `Hol(Jv)=<v,z_0> mod q`, yielding the uniform bound
`H_q(Hol(Jv))/||v||<=||z_0||`.  The explicit word lies in the commutator
subgroup of the kernel of the stable Kun--Thom double map to `Q*Q`, so all covers proposed in
`FALSE_EXPLICIT_FP_RADICAL_DOUBLE.md` are inert for modular holonomy and its
tensor amplifications.  A surviving FALSE tower must have genuinely
varying action kernels with no common commutator filling of the marked word.

Rayleigh selection cannot reduce that comparison to individual vector
states; see `TRUE_ONE_ROOT_VECTOR_STATE_NO_GO.md`.  Although every normalized
trace ratio has a vector-state ratio at least as large, every quotient
`F/N`—with no soficity assumption—has exact finite permutation models at one
distinguished root on every finite word window.  Complete the generator
partial bijections on a finite Schreier ball.  The resulting root coefficient
equals `1_N` exactly on the window.  Hence vector-state/Fell approximation is
vacuous here: TRUE is the passage from one good root to a density-one set of
good roots, and the irreducible reduction must retain normalized trace or
macroscopic rank.

The Bernoulli-lamp detour is also sharply delimited by `(BL1)-(BL4)`: the
shift action on `directSum_Gamma C_2` is a sofic `C`-action only if `Gamma` is
already sofic.  Hence both Hayes--Sale wreath-product permanence and its 2026
Alekseev--Bradford action generalization are circular for this purpose.

IRS tensor powers `(ICE1)-(ICE3)` extract the normal probability-one core and
preserve both co-hyperlinearity and co-soficity.  This turns a general IRS
separation into a group separation only when the extracted core still fails
the corresponding finite-action approximation; known subgroup-test
separations do not supply that extra property.

Spectral compression `(SCR1)-(SCR10)` now removes exceptional vectors from a
finite hyperlinear table: on an asymptotically full corner every selected
normal relator is operator-norm small, while one outside witness remains
Hilbert--Schmidt separated.  The exact residue is generator invariance of the
corner.  Averaging the defect operator over conjugates makes this a Følner
boundary problem and therefore recovers only the known amenable case.

The quantitative-stability audit `(QSA1)-(QSA5)` rules out two apparent
shortcuts.  Dor-On--Hall--Kachkovskiy requires the very operator-norm corner
leakage missing in `(SCR10)` (small normalized-HS leakage does not imply it,
even for a codimension-one corner).  Dogon--Vidick corrects special
lamplighter relations to an exact unitary representation through towers for
the amenable `Z`-shift, and explicitly does not obtain permutation rounding.
Thus pairwise unitary correction cannot replace simultaneous finite-set
assembly.

Finite-prefix completion `(FPC1)-(FPC12)` nevertheless bypasses `(SCR10)`
for every fixed word test without averaging.  Intersecting finitely many
translated good corners loses at most `|B|(1-tr(p))`; each generator then
extends from all of its tested prefix fibers to a unitary on `pH`.  Every
tested word agrees with the original word on the common large intersection,
so relators remain small and the witness remains trace-visible.  This removes
generator invariance as the analytic bottleneck.  What remains is a joint
atom/matching construction from those overlapping prefix fibers.  It may not
require the generator matrices themselves to be close to permutation
matrices—that stronger pointwise demand is false—but it must retain all
tested relator and witness losses in one finite action.

The Cartan-to-monomial estimate `(CTM1)-(CTM16)` in
`notes/TRUE_CARTAN_MONOMIAL_GATE.md` gives a dimension-free intermediate
criterion.  If the completed table approximately preserves one common masa,
Birkhoff matching puts every generator within squared normalized-HS distance
`2 kappa_D` of a monomial unitary, and multiplication passes to the underlying
permutations.  A separate fixed-phase half-plane condition then converts trace
separation into Hamming separation.  Thus a common Cartan and noncancelling
fixed phases would finish the TRUE lane; neither follows yet from the normal
`0/1` character law, and approximate Cartan invariance alone is insufficient.
Without the half-plane condition, the same construction gives an exact
abelian-by-sofic decomposition: the kernel of the permutation-ultraproduct map
is asymptotically diagonal and hence abelian.  This does not imply soficity in
the required extension orientation; `(AB1)-(AB3)` are an explicit
abelian-by-residually-finite nonsofic calibration.

The phase kernel has additional exact structure, proved in
`notes/TRUE_HAAR_PHASE_KERNEL.md`: its coordinate phases form a measurable
field of characters whose law is Haar on the Pontryagin dual, equivariantly
for the sofic quotient (`(HPK1)-(HPK12)`).  The remaining conversion is now a
finite-window Fourier-completion gate `(HPK13)-(HPK18)`: replace the
`L^2`-multiplicative Haar character chart by finite-order phase labels whose
cocycle equations hold outside `o(1)` of the coordinates.  Such a completion
untwists to permutations and is sofic, even when the phase orders grow.
Haar genericity alone does not provide the completion; the Kun--Thom
augmentation kernel specializes to the same infinite-dimensional dual action.
A valid positive special case is split extension by a finitely generated
abelian kernel, which embeds in `Hol(K) times Q`; the Kun--Thom kernel has
infinite abelian rank and therefore lies exactly outside this case.

The principal skew-product reformulation gives a direct relation-theoretic
proof for every countable-range circle cocycle.  If `lambda` is cohomologous
into a countable subgroup `A<T`, then `R_Q(lambda)` is a subrelation of
`R_Q times S_A`, where `S_A` is the hyperfinite translation relation of
`A action T`.  Product and subgroupoid permanence make the skew product
sofic, and principalization then makes `Gamma` sofic (`(HPK9cc)-(HPK9cf)`).
The same bounded-phase conclusion was already implicit in Theorem 3A, since
countable range of `lambda=b^m` forces countable range of `b`.  Thus finite
generation, property `(T)`, and Pruefer scalar divisibility are irrelevant in
the countable-range case.  A surviving bounded-exponent residue must have no
countable-range gauge on any finite-index restriction.

The exact countable-range hypothesis can now be weakened to a closure
hypothesis.  For the essentially-free quotient action, if circle cocycles
`lambda_n` with countable-range gauges converge in measure, generator by
generator, to `lambda`, then their sofic skew-product relations converge in
all finite labelled statistics to `R_Q(lambda)`.  Essential freeness keeps
every nontrivial-word fixed-point statistic identically zero, avoiding the
rotation discontinuity in the property-MD no-go.  Hence `R_Q(lambda)` and
then `Gamma` are sofic (`(HPK9cg)-(HPK9ck)`).  The surviving target is now
outside the convergence-in-measure closure of all countable-reducible
cocycles, a sharper condition than uncountable essential range.

Package that boundary as
`H^1_cr=Z^1/closure(Z^1_cr)`, where `Z^1_cr` consists of cocycles
cohomologous into countable circle subgroups.  It is a genuine quotient
because `Z^1_cr` is a subgroup, and `closure(B^1)` lies inside its kernel.
Thus a live phase residue has nonzero `H^1_cr` class on every relevant
finite-index restriction.  Do **not** call `lambda=b^m` a special density
hypothesis: every circle cocycle has a measurable pointwise `m`th root `b`
with `delta b` in `mu_m`.  Any further TRUE argument must use compatibility
of the particular root/curvature with the evaluated extension cocycle and
the Haar character field, not merely the power equation (`(HPK9cl)-
(HPK9cq)`, `(TWT32)-(TWT38)`).

Calibration: Bezuglyi--Sanadhya's density of coboundaries for hyperfinite
Borel actions gives `H^1_cr=0` there (`(HPK9cr)`, `(TWT39)`), recovering the
amenable endpoint.  No such density result is known for arbitrary principal
sofic relations.

Every circle skew product has a canonical vertical wreath envelope.  The
fiber rotations `V_(r,s)(x,t)=(x,lambda_r(sx)t)` generate a hyperfinite
relation normalized by the lifted base action, and together they form an
action of the abstractly sofic restricted wreath product
`(directSum_Q Z) wr Q`.  The skew action lies inside this envelope
(`(HPK9cs)-(HPK9cx)`, `(TWT40)-(TWT45)`).  This does not close the gate:
soficity of the abstract wreath product does not make this particular action
sofic.  Coordinatewise torsion quantization respects the base shift but can
destroy vertical kernel relations, including the cocycle identity; a tiny
carry moves the whole phase fiber.  The live statement is soficity of this
specific wreath action, equivalently the relation-preserving completion
`(HPK18)`.

Universalize the same gate via the projective full shift.  Every cocycle has
the equivariant orbit-configuration factor
`Phi_lambda:X->P_Q=T^Q/T`, and is the pullback of
`c_q([f])=f(q)/f(1)`.  The skew action on `X times T` is exactly the
relatively-Haar fiber product
`{(x,f):[f]=Phi_lambda(x)}` with the shift on `T^Q`
(`(HPK9cy)-(HPK9dh)`, `(TWT46)-(TWT51)`).  This quotient is exactly Popa's
factor map.  Austin's property-`(T)` examples show that universal
model-surjectivity is false: good projective models may live in nonzero
finite-graph cohomology sectors a uniform distance from every global vertex
potential.  This does not obstruct finite-phase completion: Austin's
bad models are already exact circle cocycles, and torsion points are dense in
the exact-cocycle subgroup of every finite chart.  The live theorem is
therefore different, not merely weaker: select **one** model sequence,
compatible with the given base colors and relatively-Haar joining, for which
vanishing raw cocycle defect forces vanishing distance to the exact cocycle
locus.  Torsion density then supplies finite-phase equality away from `o(1)`
vertices.  This is exactly the qualitative cocycle-stability gate
`(CS1)--(CS8)`, not a choice of cohomology sector.  The Popa audit is in
`notes/POPA_FACTOR_MODEL_LIFTING.md`.  Product permanence still uses the
wrong, independent joining.

Complete-simplex unfolding does not bypass this gate.  On `V times F`, the
label potentials make the phase transitions an exact coboundary and permit
exact torsion rounding, but completing the partial translations
`q |-> gq` costs `|gF triangle F|/(2|F|)`.  This vanishes along an
exhaustion exactly in the Følner/amenable case.  Identifying the local copies
through `(v,q) |-> sigma_q(v)` removes that boundary only if the rounded
phases agree on overlaps, which is `(CS1)` again.  The proof and quantitative
boundary estimate are in `notes/PHASE_UNFOLDING_AMENABILITY_BARRIER.md`.

For a phase kernel of exponent `m`, the section primitive has an intrinsic
Bockstein residue.  Writing `delta b(q,r)=a_(v(q,r))`, the functions
`lambda_q=b_q^m` form a measurable circle-valued 1-cocycle.  If `lambda` has
an `m`th root **inside the 1-cocycle group**, then dividing `b` by that root
produces a `mu_m`-valued monomial embedding; skew untwisting proves soficity
(`(HPK9e)-(HPK9k)`).  Pointwise divisibility of the circle does not imply
cocycle divisibility.  Thus any bounded-exponent common-Cartan counterexample
must carry a nonzero Bockstein residue; this is the exact cohomological datum
which finite cocycle stability would have to eliminate.  Concretely the
residue is the evaluated extension class
`partial_m[lambda]=[a_(v(q,r))]`; it maps to zero in circle-valued `H^2`, so
injectivity of `H^2(mu_m)->H^2(T)` for the Loeb action would close this gate.
This injectivity is not automatic even in an exact regular model: the
four-dimensional regular representation
`C_4 -> U(4)`, `g |-> swap directSum i directSum (-i)`, has phase kernel
`C_2`, Haar kernel law, and nonzero Bockstein (`(HPK9m)-(HPK9p)`).  The same
group is sofic through another Cartan.  Therefore the residue is a
model-level obstruction; a general proof must replace the Cartan or round
through it, not try to deduce its vanishing from trace moments.

Slow tensor amplification performs one useful model replacement.  Taking
`L_n`-fold tensor powers with `L_n->infinity` sufficiently slowly preserves
all multiplicativity and the kernel `K`, while changing every nontrivial
quotient permutation length `ell` to `1-(1-ell)^(L_n)->1`.  Hence the
quotient Loeb action may be assumed essentially free.  For exponent-`m`
kernel, the remaining residue lies in the coefficient kernel
`ker(H^2(R_Q,mu_m)->H^2(R_Q,T))` of a principal sofic equivalence relation.
It vanishes when `R_Q` is treeable.  The exact remaining TRUE-side question
is whether the special residue forced by a monomial hyperlinear model can be
removed for arbitrary principal sofic `R_Q`.

Popa superrigidity gives a sharp negative calibration to automatic removal.
For the free Bernoulli relation of
`Q=SL_3(Z) times C_m`, the projection character `Q->mu_m` is not
`m`-divisible in measurable `H^1`.  It occurs as the phase residue in a
regular common-Cartan model of the residually finite group
`SL_3(Z) times C_(m^2)`.  Thus even principal sofic relations may retain the
minimal-alphabet residue; the group is sofic only because its phases already
lie in the larger fixed alphabet `mu_(m^2)`.  The true target remains
finite-phase completion, not universal Bockstein vanishing.

This target sharpens once more if all torsion phases are allowed.  Put
`mu_infty=union_M mu_M`.  A measurable `mu_infty`-valued primitive can be
truncated on each finite test to one alphabet `mu_(M_n)`: only finitely many
functions occur, their discarded mass tends to zero, and the projective
cocycle equation then fails only on the union of three discarded sets.
Finite-phase skew untwisting proves soficity.  The same proof works for every
torsion phase kernel, without a global exponent: a finite test sees only
finitely many kernel orders and `M_n` can absorb them.  Consequently the
exact torsion-kernel obstruction is now

`ker(H^2(R_Q,mu_infty) -> H^2(R_Q,T))`,

not the larger minimal-alphabet Bockstein kernel.  Both the `C_4` and
Popa/Bernoulli calibrations vanish after this enlargement (`mu_4` and
`mu_(m^2)`, respectively).  Finite-index permanence for sofic relations is
not a shortcut: it assumes the base subrelation is already embedded in the
finite extension, while constructing that subrelation is exactly the
torsion splitting being sought.

The coefficient kernel also has an exact primitive quotient description:

`ker(H^2(R_Q,mu_infty)->H^2(R_Q,T))`
` ~= {b:delta b is torsion-valued}/(T-valued cocycles * torsion cochains)`.

This gives a positive criterion.  If, after multiplying the circle primitive
by a circle 1-cocycle, its scalar essential range is countable, divisibility
of the roots of unity extends the identity on the torsion intersection to a
scalar homomorphism.  Applying it pointwise produces a measurable torsion
primitive and proves soficity (Theorem 3A in
`notes/TRUE_HAAR_PHASE_KERNEL.md`).  The unrestricted coefficient statement
already fails for a free hyperfinite relation in degree one: the cocycle
`u(a,x)=a` for dense translations `Q/Z acting on R/Z` is a circle
coboundary but not a `Q/Z` coboundary.  The live target must therefore use
the special automorphic Haar evaluation `omega(q,r,x)=chi_x(v(q,r))`, not a
generic measurable retraction.

There is a second exact endpoint which does not demand splitting.  The
torsion twist `Sigma_omega=mu_infty times_omega R_Q` contains `Gamma` in its
full group via the bisections `x |-> (a_k(x),q,x)`.  Essential freeness and
the Haar law give every nonidentity bisection positive metric length, so
soficity of `Sigma_omega` would imply soficity of `Gamma` after product
amplification.  This is not automatic from soficity of `R_Q`: universal
finite-twist permanence would already settle the open finite-central-kernel
extension problem.  The two live alternatives are therefore torsion splitting
or direct sofic approximation of this special evaluated-extension twist.
There is an intermediate virtual criterion: it is enough for the torsion
class to vanish on a finite-index subrelation.  Its full preimage retains all
torsion isotropy, is a sofic product groupoid by Cordeiro's product theorem,
and has finite index in the whole twist; Cordeiro induction then applies
noncircularly.  In particular Kida's treeable cohomology vanishing shows that
a finite-index treeable subrelation closes the phase gate.
For bounded-exponent kernels, character-rigid quotient actions also close:
every character of a finitely generated `Q` becomes `m`-divisible on the
finite-index preimage of `m Z^r directSum 0<Q_ab`.  Thus the Popa carry
calibration is globally nonsplit but virtually split.  The remaining
bounded-exponent obstruction must stay non-character-like under every
finite-index restriction.
More generally, if `lambda` is cohomologous to a cocycle taking values in
any finitely generated subgroup `A<T`, restrict to the finite-index kernel
of `A -> A/(m Z^d directSum 0)` and divide the remaining free coordinates by
`m`.  Hence a surviving phase class must have essentially infinitely
generated scalar range after every gauge and every finite-index restriction.
For an ergodic property-`(T)` quotient action, even countable range closes:
the skew-product representation on `L^2(X,ell^2(A/A_0))` turns a large
finite range truncation into an almost invariant vector, and its invariant
repair has a unique dominant coordinate which gauges the cocycle into
finitely generated `A_0`.  The scalar method is sharp at Pruefer
`p`-torsion, where multiplication by `p` has no right inverse and there are
no proper finite-index subgroups.
Mackey's compact-cocycle reduction sharpens the invariant boundary further:
on every finite-index ergodic restriction, a proper Mackey subgroup of the
circle is finite and therefore closes by the virtual finitely-generated
range theorem.  Any surviving residue must have full circle Mackey range on
all such restrictions.  Moreover `lambda=b^m` cannot itself be
torsion-valued: that would force `b` to be torsion-valued and give the
torsion primitive immediately.  Pruefer behavior can arise only after a
genuinely non-torsion transfer.
The unsplit Bockstein has a principal endpoint as well.  Its fixed-alphabet
root groupoid acts freely on `X times T`; the resulting relation is exactly
the finite amplification `R_Q(lambda) times (mu_m)^2`.  The action embeds
the root groupoid full semigroup trace-preservingly into this relation.
Hence soficity of the ordinary circle skew-product relation `R_Q(lambda)`
already proves soficity of `Gamma`.  In the Mackey-full case this skew
product is ergodic.  Universal compact-skew-product permanence remains
unavailable and would cross the finite-central-kernel boundary.

Next: extract a finite matching system from the simultaneous prefix-fiber
data `(FPC4)-(FPC8)` without demanding generatorwise matrix approximation.
Use the normal `0/1` trace law to control overlaps and retain only the tested
word losses.  Do not route through conjugate
averaging, amenability, generic HS stability, or Bernoulli-lamp permanence;
their exact stopping points are now proved in the notepad.

Also do not demand metric-sofic approximation of `U(d)`.  The scalar
prime-order subgroup with chordal HS length has unequal nonidentity lengths,
whereas an approximate permutation action of `C_p` forces every nonidentity
power to have the same asymptotic Hamming length (`(MSU1)-(MSU4)`).  The
normal-Dirac problem is narrower because it only retains a limiting discrete
`0/1` word law after table-dependent amplification.

The canonical Schoenberg/Poisson scalar transform does not cross the gap
either.  Applied to the nonnegative `C_4` character `(NIR5)`, it gives
`(1,e^(-t),e^(-2t),e^(-t))`, which violates the finite-action inequality
`theta(g)<=theta(g^2)` for every `t>0`; the violation persists after every
finite tensor amplification (`(SPF1)-(SPF6)`).  Only the limiting normal
`0/1` character removes it.  Do not replace the joint matching problem by a
generic negative-type-to-fixed-point transform.

Do not confuse Lueck's ``approximation property'' for permutation characters
with density of permutation characters.  In the precise definition audited in
Boschheidgen's thesis, it says only that von Neumann ranks converge along a
pointwise-convergent sequence already lying in the permutation-character
class.  It neither produces that sequence nor moves a finite-dimensional
unitary sequence into the class.  The same warning applies to Kionke's
fixed-algebraic-degree version; see `(LRA1)-(LRA5)` in `notes/NOTEPAD.md`.

Exact-image functoriality is also impossible, even for a fixed normal-Dirac
table. The cyclic two-dimensional sequence `(IFR1)-(IFR8)` converges
pointwise to the regular character of `C_2`, but its exact images satisfy the
changing accidental relation `b=a^(2n)`. Every finite action of those images
has `supp(b) subset supp(a)` and cannot approach the target values
`chi(a)=1`, `chi(b)=0`. Hence residual finiteness of the matrix/projective
image, its regular or coset actions, and same-image permutation-character
conversion are dead routes. The output must forget accidental levelwise
relations; see `notes/TRUE_IMAGE_FACTOR_NO_GO.md`.

FALSE-side fermionic criterion: the full exterior-algebra functor turns one
operator-norm-visible eigenvalue into a uniform normalized-HS displacement.
After tensoring it with its conjugate, the normalized character is
`|det((1+U)/2)|^2` and the normalized-HS multiplicative defect is at most
`sqrt(d_n/2)` times the original operator-norm defect. Hence a radical
witness with a model satisfying `sqrt(d_n) * defect_n -> 0` already yields a
hyperlinear nonsofic quotient. This removes every rank-profile requirement
and leaves only a quantitative
dimension--error gate; see `notes/FALSE_FERMIONIC_AMPLIFICATION.md`.
The same note now proves that this square-root loss is optimal up to a
universal constant among all exact continuous functorial amplifications:
if `R:U(d)->U(N)` makes a rank-one involution HS-visible by `Delta_R`, then
its normalized-HS differential has operator-to-HS norm at least
`sqrt(d) Delta_R/pi`. Therefore the next FALSE step must use special group
structure rather than swap in a more efficient universal representation
functor. More generally a rank-`r` visible involution costs at least
`sqrt(floor(d/r)) Delta/pi`, recovering the `1/sqrt(delta)` sparse-corner
scale for relative rank `delta=r/d`.

FALSE-side no-go `(CAF1)-(CAF13)`: a fixed-point-free element of an amenable
action survives the sofic image obtained by completing its restrictions to
Følner sets.  Therefore every coamenable subgroup contains every central
element of `Rad_sof(J)`, and a class-`A` group has
`Z(J) intersect Rad_sof(J)={1}`.  This rules out all coamenable monomial
negative sectors for the cyclic shear, including nonnormal character
induction.  See `notes/FALSE_COAMENABLE_ACTION_CRITERION.md`.
Do not pursue class-`A` permanence as an allegedly weaker shortcut.  The
Følner-truncation theorem already forbids the required fixed-point-free
action.  Conditionally, the displacement collapse `(CAC9)--(CAC15)` proves
that any such shear action
already restricts on one vertex to an amenable action in which the original
radical witness moves mean mass at least `1/4`; that restricted action itself
produces the hyperlinear nonsofic image.  The smaller action target is
directly an amenable `H`-action with `m(Fix(x))<1`.

The prescribed-mean strengthening `(CAP1)--(CAP13)` closes that smaller
target too.  After pullback along a free presentation, every invariant-mean
permutation character is a pointwise limit of finite-action characters:
approximate the chosen mean by an
`ell^1`-Reiter sequence, replace rational weights by numbered fibers, and use
the coherent partial maps `(x,k)|->(gx,k)`.  Their unmatched mass is the
`ell^1` boundary and their common fiber indices make multiplication coherent.
Thus a sofic-radical element has fixed-set mean `1` in every amenable action.
Any viable amenable negative sector must be genuinely nonpermutational, not
merely nonmonomial.

The action-level gauge reformulation does not provide a shortcut through
known hyperlinear targets.  In the Alekseev--Bradford definition, if an
action is a sofic `C_2`-action but not a sofic `C_1`-action for nested group
classes `C_1 subset C_2`, then at the finite window witnessing failure for
`C_1`, the auxiliary target `Lambda` supplied by `C_2` already lies in
`C_2 minus C_1`.  Hence the explicit gauge action being hyperlinear-sofic
but not sofic would already produce a finitely generated hyperlinear
nonsofic target before forming its semidirect product.  Finite groups and
fixed-dimensional linear targets cannot witness that window because they
are sofic.  The computational action endpoint is therefore an explicit
finite obstruction window plus a cross-level tracial-ultraproduct
realization, not a one-level automorphic covariance search.  See
`FALSE_ACTION_APPROXIMATION_NO_SHORTCUT.md`.

The Kazhdan-corner theorem gives a separate exact FALSE certificate: every
nontrivial weak-MF Kazhdan group has a nontrivial hyperlinear quotient, by
renormalizing on the complement of the central Kazhdan projection.  Hence a
simple Kazhdan weak-MF group is hyperlinear, and weak MF of
`St_5(L_(F_2)(1,2))` would make its simple nonsofic quotient
`EL_4(L_(F_2)(1,2))` hyperlinear.  See
`notes/FALSE_KAZHDAN_CORNER.md`.  Do not treat Delzant's theorem that every
countable group embeds in a Kazhdan group as MF-preserving: its envelope is
a quotient `P/N` of an SQ-universal hyperbolic Kazhdan group, and weak MF is
not known to pass through the arbitrary quotient `P->P/N`.

Do not try to extend Pestov's invariant `UCB` sphere mean to all bounded
functions formally.  The implication is false even in dimension two:
a faithful `F_2<SU(2)` representation is Bekka-amenable and has the Haar
mean on `UCB(S^3)=C(S^3)`, but its sphere action is free, so an invariant
`ell^infinity(S^3)` mean would contradict paradoxicality of `F_2` (`(USP4)--
(USP5)`).  A sphere route must use the normal `0/1` trace law essentially.
In fact odd symmetric powers sharpen the warning: their exact normalized
characters converge to the regular `0/1` character of `F_2`, and every
level still acts freely on its unit sphere, so no invariant
`ell^infinity`-mean exists (`(USP6)--(USP9)`).  The normal law cannot justify
a levelwise extension; it would have to enter through a cross-level matching
argument.

The collaborator's universal cyclic-module candidate and exact coinduced
parity model are the same analytic target.  Fourier transform on
`A_univ` identifies the signed coinduced crossed product with the normalized
`z=-1` central corner `p_-L(E_univ)`; at the reduced C-star level,
`A_(G,s)=p_-C_r^*(E_univ)`.  The `z=+1` corner is the ordinary wreath
quotient.  Thus the FALSE gate is exactly MF/Connes embeddability of one
explicit negative central corner, not a choice between two representations.
The proof and the precise non-permanence warning are in
`notes/COINDUCED_NEGATIVE_CENTRAL_CORNER.md`.

## 2. Defect-localized commutant pinning  [LEMMAS LANDED]

The (T)-analog of the kernel-checked f.d. collapse (N20), avoiding the
HS-stability wall.  The interface is now kernel-checked in
`Sofic/CommutantPinning`: (L1) `exists_mem_close_of_almost_le` — a
subspace δ-almost contained in an equal-dimensional subspace is
δ/(1-δ)-almost equal to it; (L2) `dist_le_defect_div_gap` and
`dist_le_perturbed_defect_div_gap` — gap pinning against exact and
ε-perturbed operators, with `sum_apply_dist_le` transferring closeness
through averaging.
Conjecture: for the Kun–Thom pairs, the model defect can be localized off
a relative-(T) core whose exact commutant then pins the almost-commutant;
one pinned compressor conjugate kills the free-lamp witness — T4 on the
family without Gate 1.

## 3. The approximation radicals  [FORMALIZABLE FRAME]

`𝔰(G)` (sofic radical) and `𝔥(G) ⊆ 𝔰(G)` (hyperlinear radical) over the
repo's `UniversalSofic`/hyperlinear ultraproducts.  Q3.4 ⟺ 𝔥 = 𝔰 on f.g.
groups.  The finite-presentation localization `(FPR1)-(FPR12)` sharpens this:
it is enough to prove equality for finitely presented groups, and any failure
is detected by one element in one finite presentation.  Conjecture:
`𝔰(H_K)` is the whole lamp kernel.  A strict
intermediate value of `𝔥(H_K)` would be a canonical invariant of the
hyperlinear–sofic gap — bigger than either answer.

## 4. The closure-exactness dichotomy  [ORGANIZING PRINCIPLE]

Four kernel-checked-or-measured instances this session: profinite closure
swallows the normal closure; f.d. commutants are rigid; liftable models
absorb totally; exact-coherence strata absorb totally.  Working thesis:
for compressed pairs, every closure-exact approximation category totally
absorbs, and Q3.4 on these families asks exactly whether HS-with-(T) is
closure-exact.  Dig where closure-exactness breaks: the normal `0/1`
character-transfer problem (item 1), and controlled inexactness (item 2's
ε-budget).

## 5. Two-chart atlas computation  [FIRST SIGNAL]

The MSI experiment in `experiments/atlas_two_chart_results.md` translates 54
exact Steinberg/Leavitt relations through the explicit `A8*A8` atlas and
tests all 648 centrality constraints obtained from twelve chart generators.
Exact `F_2` Leavitt reduction validates every source relation.  At
multiplicities `k=1,2,4`, worst-tail optimization reduces the maximum
normalized-HS defect only

`1.27256 -> 1.24958 -> 1.23908`.

The gain is genuine but slow.  Exhausting all 40,320 automorphisms of `A8`
finds no exact classical alignment: the best inner alignment satisfies
`42/54` source relations and the best outer alignment `20/54`.  Thus the
subsystem has nonclassical multiplicity daylight but no near-solution.
Next: extract the full finite normal-relator list before larger blind runs;
in parallel, target the persistent scalar Steinberg/Cuntz branch for a
dimension-free trace or SOS inequality.

The natural-eight-point red-team in
`experiments/atlas_one_involution_results.md` adds the commuting-Boolean
geometry from the current one-involution FALSE endpoint.  GAP's exceptional
isomorphism `GL_4(F_2) ~= A8` makes a chart transvection four disjoint
2-cycles, so a diagonal involution can be chosen exactly antipodal.  At the
best classical inner alignment, all 78 conjugate-commutator tests vanish
exactly while the 648 atlas constraints have RMS defect `0.46811943`.
Multiplicity two lowers this only to `0.46792161`, with orbit RMS
`0.00567036`; the atlas operator maximum remains `2`.  Thus the finite
Boolean sector does not cause the atlas floor, but the observed improvement
is merely local perturbative daylight.  Do not scale this blind.  The same
scalar `e/E` Steinberg--Cuntz branch remains the dual/SOS target.

On the direct FALSE lane, Corollary 10 of
`FALSE_MACKEY_SPLIT_COCYCLE.md` lowers the final one-involution endpoint from
operator norm to normalized Hilbert--Schmidt norm: finite telescoping of the
unitary products and commuting lamp factors passes directly to the tracial
ultraproduct.  Operator norm remains relevant only for the stronger MF
statement.  The coinduced parity model already realizes antipodality and all
commuting conjugates exactly in a finite crossed product, so the direct
matrix problem is now approximation of that explicit crossed product while
retaining its radical sign, not construction of the infinite-dimensional
parity action.

`FALSE_RF_VERTEX_HS_MATCHING_NO_GO.md` closes the most immediate use of the
new residually finite vertex decomposition.  For the special Kun--Thom fold
word `s=i_2(h)i_1(h)^(-1)`, property `(T)` implies that any two honest
finite-dimensional representations of the RF vertices whose restrictions
become normalized-HS compatible on the common edge satisfy `s->1`.
Asymptotic amalgam gluing and `z=[v,s]` then force `z->1`; equivalently the
negative spectral rank is `o(d)`.  Thus even tracial matching of arbitrary
exact RF vertex models cannot solve the FALSE endpoint.  At least one vertex
must already be represented by a genuinely nonliftable HS
almost-representation.

The one-orbit clutching refinement does not evade this no-go by implementing
the lamp shear exactly.  The same note proves the quantitative bound: if
exact vertex representations agree on `A_s` and the central involution has
negative relative rank `delta`, their mismatch on a fixed Kazhdan set of
`Gamma` is at least `(kappa/2)sqrt(delta)`.  In particular an exact global
Boolean flip with `z=-1` leaves a dimension-independent edge defect of at
least `kappa/2`.

The first cohomological-code spectrum calibration is in
`experiments/phase_code_spectrum_results.md`.  Exact locally free `F_2`
Schreier charts can have a two-block bottleneck with only two cross-half
generator edges.  Their binary half-word has check defect `1/n` but distance
`1/2` from the degree-zero cocycle code, while the first positive incidence
singular value is asymptotic to `2/sqrt(n)`.  MSI sparse spectra through
`n=4096` reproduce this law; random Schreier controls retain gap about
`0.72`.  Thus neither soficity, essential freeness, nor local statistics
alone can give the uniform repair spectrum suggested by `(PFL11)`.  A TRUE
decoder must select expanding/cosystolic charts or exploit the prescribed
relatively-Haar joining; arbitrary-chart spectral mining is a dead route.

The first genuine degree-one selected-chart computation is in
`experiments/sl3_degree_one_spectrum_results.md`.  For the fixed six-root,
13-relator presentation of `SL_3(Z)` acting on `F_p^3-{0}`, sparse MSI runs
through `p=37` give coexact degree-one singular bottoms between `0.7678` and
`1`, on complexes ranging from 156 to 303,912 edges.  This is evidence for
a linear repair estimate on these selected property-`(T)` charts, not a
uniform-gap proof and not yet circle/torsion repair.  More importantly, the
lowest modes split exactly under the commuting scalar `F_p^*` action: the
`p=23` anomaly is wholly in the quadratic-character block, while the `p=37`
mode is wholly scalar-invariant.  Stop extending the raw prime table.  The
scalar-character Fourier reduction is now implemented and validated in
`experiments/sl3_character_block_spectrum.py`; at `p=37` it reduces 303,912
edge coordinates to 8,442 per block and reproduces the full minimum to
`1e-14`.  An all-character pass shows that primitive, quadratic, and trivial
characters can each be the winning sector.  Any certificate search therefore
had to control every character order rather than extrapolate one block.

That certificate search has succeeded in a stronger universal form; see
`TRUE_SL3_HODGE_SOS.md`.  A 102-by-132 rational group-ring factor and an
exact coefficient residual prove

`Delta_1 >= 14164556740143/5000000000000000 I`

for the fixed `SL_3(Z)` presentation in every unitary representation.  This
makes the qualitative property-`(T)` result in
`TRUE_PROPERTY_T_LINEAR_COCYCLE_GAP.md` explicit and gives

`dist(a,Z^1) <18.789 ||d1 a||`.

The real-linear selected-chart gate is therefore closed.  Do not spend more
compute on its character blocks.  The live obstruction is integral and
nonlinear: lift circle phases through integer carries, retain the
finite-order cohomology class, and turn `L2` repair into Hamming deletion.
On the FALSE side the same issue asks whether varying torsion curvature can
evade real repair and furnish the genuinely nonliftable projective sector.

`TRUE_INTEGRAL_CARRY_TRANSVERSALITY.md`, Proposition 4, also closes the
tempting universal generalized-inverse search.  For any infinite one-ended
finitely presented group, `DBD=D` over `Z[G]` would split `ker D=im d0`;
augmentation makes that impossible.  In particular it cannot hold for
`SL_3(Z)`.  The surviving compute target is chart-dependent: measure or
construct the finite carry lattice `ran(d1_V) intersect Z^cells` and its
transversality, not one universal integral group-ring splitting.

The first such audit is in `experiments/sl3_carry_results.md`.  Basis
leverage through `p=37`, exhaustive two-cell searches, torsion-cell LLL at
`p=3,5`, and a full-cell LLL pass at `p=3` find no divergent carry.  The
strongest class is always the fixed-axis CRW torsion cell and stabilizes at
`Theta>=4.543096`.  Exact Smith arithmetic gives saturation quotient `C_3`
at `p=3`; at `p=5`, three cold-verifiable maximal minors have determinant
gcd one, proving that the relator image is saturated.  This is positive
signal for bounded carry transversality, not an upper bound.  The next
solver must synthesize a uniformly bounded chart-dependent integral
reduction operator or exhibit a long carry with projected norm tending to
zero.  Dense Smith forms are superseded by sparse modular selection and
exact determinant/gcd certificates.

The saturation computation is not the terminal invariant.
`INTEGRAL_CARRY_DISCRIMINANT_DUALITY.md` proves that `Theta` is governed by
the discriminant gluing of the primitive cycle lattice
`ker(d1^T) intersect Z^cells`; saturation of `im(d1)` neither bounds nor
forces it.  The next autonomous solver must therefore construct the cycle
Gram discriminant module and certify the paired closest-vector radii, using
the scalar/chart symmetries to avoid unrestricted high-dimensional CVP.

The first exact cycle computation confirms that requirement.  At `p=3`,
the primitive cycle lattice has rank 207 and a 296-bit discriminant with 13
nonunit Smith factors; the fixed-axis cell alone has enormous class order
but squared distortion only `20.612266...`.  Exhaustive class enumeration
and class-order heuristics are therefore both dead.  Exact combined-map
minor certificates also prove full constant-cycle transfer at `p=3,5`, in
agreement with the Schur-multiplier theorem.  Continue only in genuinely
new-cover symmetry sectors of the cycle discriminant module.

The cover Hopf quotient now makes "new-cover" precise.  For `X=G/H`, if
`Sigma_X` is the subgroup of the cycle lattice represented by lifted
spheres, then

`K_X/Sigma_X ~= H_2(H,Z)`.

Because `SL_3(Z)` is of type `F_infinity`, `Sigma_X` is generated by the
lifts of finitely many bounded spherical templates.  Thus the full carry
gate has two exact parts: norm-controlled integral decoding in that local
spherical lattice, and discriminant control for the varying stabilizer
Schur multipliers.  Finiteness of `H_2(SL_3(Z),Z)` closes neither part; it
only closed the already-separated transfer of base cycles.

The scalar-involution audit makes those sectors explicit.  The integral
plus/minus split has index `2^103` at `p=3`; its gluing codes are
`[169,103]` and `[806,495]` at `p=3,5`.  They contain many weight-one words,
so cosystolic expansion is false, but weight-at-most-four words generate
only ranks `61` and `157`, so a bounded local-generator proof also fails at
the first tested bound.  The next TRUE solver must price high-support
binary gluing in the sector Gram norms.  Do not infer distortion from code
dimension, minimum weight, or discriminant-class order alone.

The exact involution-overlattice formula performs the needed algebraic
compression.  If `K_0=K_+ directSum K_-` and `C=K/K_0` is the binary gluing
code, then

`D_K ~= C^perp/C`,

and each shortest discriminant radius is a weighted nearest-code distance,
the sum of its two sector Gram distances minimized over `C`.  Odd-primary
torsion splits completely between the two sectors; only the two-primary
part is coupled by the code.  A codeword of support `w` has prequotient
squared sector cost at least `w/2` in each sector.  Thus the live invariant
is the nearest-code radius in the sector metrics, not whether high-support
codewords admit a bounded-support generating set.

The gluing code itself is the homology image for the scalar two-cover:

`C=im(H_2(P_H,Z)->H_2(P_J,F_2))`.

The long exact sequence of the integral trivial/sign local systems says it
is also the kernel of one connecting map.  After quotienting the spherical
subgroup, its exact nonspherical part is

`im(H_2(H,Z)->H_2(J,F_2))`.

Thus low-weight codewords may be merely lifted bounded spheres.  Separate
those local templates before interpreting the measured weight distribution;
the genuinely global nearest-code obstruction is a stabilizer-homology
image, not an arbitrary binary code.

For a selected `SL_3(Z)` chart family, the scalar code can be removed
entirely: use the exact actions on `P^2(F_p)` instead of on
`F_p^3 minus {0}`.  Every fixed nonidentity integral matrix is nonscalar
modulo all but finitely many primes and then fixes at most `p+2` of the
`p^2+p+1` projective points, so this family is still asymptotically free.
The universal Hodge SOS applies unchanged.  Its carry lattice is the
trivial scalar-character sector, with no scalar gluing.  This does not
control that sector's odd discriminant or stabilizer homology, but a proof
which needs only one selected exact family should not solve the strictly
harder all-character gluing problem first.

The first exact projective-chart audit is now in
`experiments/sl3_projective_carry_results.md`.  For the point stabilizers at
`p=3,5,7`, exact Shapiro boundary complexes give rational `H_2=0` and
integral groups `C_2^3,C_2^3,C_2^4`.  The small-level boundary ranks follow
`3n+1` and `7n-1` for `n=p^2+p+1`.  This is a valuable calibration, not a
uniform theorem: prime-level cuspidal cohomology gives nonzero rational
`H_2` at later levels.  Thus the live program must control both numerator
growth on the acyclic charts and the metric harmonic lattice on the
non-acyclic charts.

The first non-acyclic chart is now computed exactly at `p=53`.  The Shapiro
complex has rational `H_2` of dimension two: its `F_101` ranks give the
upper bound two, matching the two-dimensional cuspidal lower bound of
Ash--Yasaki.  A sparse real Hodge solve isolates the same two-plane with a
gap of `0.19377` to the next eigenvalue, and 64.15 percent of its leverage
lies in one five-term degree-two cell orbit.  The live metric calculation is
therefore an exact rank-two lattice lift/regulator problem, not another
homology-dimension sweep.  See
`experiments/sl3_projective_carry_results.md`.

The compact non-free cellular model now resolves that rank-two discriminant
in its own free signed-coinvariant lattice.  Its complex has dimensions
`141<-364<-328<-112`; the harmonic quotient is cyclic of order
`17269229743444936295695902979877937666574454551881432366677092780148396252626561139`,
and the exact shortest nonintegral dual vector has norm
`0.2670563781191559`, below the spherical threshold `1/sqrt(12)`.  Positive
integral lift energy first gives a coarse compact-metric lower bound.  The
shortest class is now solved exactly: saturated-range reduction finds the
four-term lift `e_240-e_287-e_302+e_304`, and exhaustive support profiles
rule out squared norm below four.  Thus its exact paired contribution is
`2sqrt(q/a)=7.489055360091924`.  A verified lift of the second reduced basis
vector has squared norm `16` and is orthogonal to the four-term lift.  Their
exact generalized section norm is `7.49017741972933`, giving the near-sharp
bracket
`7.489055360091924<=kappa_Sigma<=7.49017741972933`.  Thus the free compact
rank-two numerator is solved at `p=53`; the live question is uniformity at
later cuspidal levels, not another discriminant enumeration at this level.
The two-primary audit shows that this bridge must be derived.  At `p=53` the
zero-th signed coinvariants contain `(Z/2)^84` in degree two.  The naive
unsigned mod-two orbit complex has homology dimensions `(1,0,24,6)`, whose
degree-three value is smaller than the rational Betti number `10`; it cannot
be the reduction of a free integral comparison model.  One must splice in
fixed free resolutions of the finite cell stabilizers.  Their orders are at
most `24`, so the primary exponent is uniformly bounded even though the
number of torsion coordinates grows linearly with `p`.  See
`TRUE_P53_CELLULAR_HARMONIC_DISCRIMINANT.md` and
`TRUE_TWO_PRIMARY_CELLULAR_DERIVED_AUDIT.md`.

That splice is now identified with an existing object rather than a new
implementation task.  HAP's
`FreeGResolution(ContractibleGcomplex("SL(3,Z)"),3)` is the derived
Wall/perturbation total complex, and
`ResolutionArithmeticGroup("SL(3,Z)",3)` is exactly this construction.  Its
degree-two bidegrees have multiplicities `6,2,2` for `(0,2),(1,1),(2,0)`,
so the previously exported `28630`-coordinate level-53 complex already
contains the positive stabilizer-resolution rows.  Fixed group-ring term
counts give uniform squared Schur bounds `16,980,30906` through degree
three.  The live bridge is consequently the bounded-primary lattice defect
of the canonical filtered augmentation, not construction or real-norm
control of another complex.  See `TRUE_HAP_DERIVED_TOTAL_AUDIT.md`.

The zero-th-row residual primary boundary is now solved uniformly on the
projective family.  For every odd prime, after cancelling the first
degree-two block, the map from degree-three orientation torsion to the
second degree-two torsion block is a disjoint union of `[1 1]` repetition
rows.  The proof identifies the source with `P^1(F_p)` modulo
`t -> t/(2t-1)`, plus a possible order-four eigenline, and the target with
two copies of that quotient glued at one point.  With `chi=(-1|p)`, it has source dimension
`(p+4+chi)/2`, target dimension `p+2`, rank `(p+1)/2`, and exactly one unused
target coordinate.  Its image therefore has a local norm-one decoder; it is
not the feared high-covering-radius binary code.  The live task is to trace
the explicit kernel/cokernel coordinates through the positive
stabilizer-resolution rows.  See
`TRUE_PROJECTIVE_PRIMARY_RESIDUAL_MATCHING.md`.

The positive stabilizer rows have also been reduced without computation.
For any fixed finite cell stabilizer `H`, the specialized vertical free
resolution splits orthogonally over the `H`-orbits of the coefficient set.
Each orbit is `H/L` for one of finitely many subgroup types, so choosing an
integral boundary section for each fixed template gives a uniform vertical
decoder in every chart.  Shapiro identifies the surviving fibres as
`H_s(L;Z_chi|L)`.  Hence the remaining bounded-primary gate is only the
horizontal Wall incidence on these local homology labels and its coupling
to the free harmonic lattice.  See
`TRUE_VERTICAL_STABILIZER_DECODER_SPLITTING.md`.

The first positive horizontal complex has now been measured exactly.  On
`p=3,5,7,11,13,17`, the map
`H_1(D_8;F_2[X])->H_1(S_4;F_2[X])` has ranks
`3,4,5,7,8,10=(p+3)/2`.  Its kernel has dimensions `5,7,8,11,13,16`, and the
incoming image from the two-cell `H_1` row has exactly those same ranks.
Consequently `E^2_(1,1)=0` on all six charts: the growing edge-stabilizer
homology is horizontally exact rather than a surviving obstruction.  The
theorem target is to express this complex in orbitwise Shapiro bases, prove
exactness with a bounded local splitting for every odd prime, and then
analyze the two outer positive terms.  The latter audit is now also sharply
favorable: after `d^1` and `d^2`, the growing vertex `H_2` term has dimension
exactly two at all six levels; `d^3` is zero, so this fixed local residue is
the entire positive contribution at `E^infinity`.  Direct intersection of
the total cycle space with the cellular filtration independently gives
graded dimensions `(2,0,2),(2,0,2),(2,0,3),(2,0,3),(2,0,4),(2,0,4)`.
Thus all remaining mod-two growth lies in the two-cell zero row.  The live task is a
uniform orbitwise proof with bounded integral splittings, not control of a
growing positive-row rank.  See `TRUE_PROJECTIVE_DERIVED_E1_AUDIT.md`.

The constant positive residue is itself visibly local.  At `p=3,5,7`, the
first vertex-resolution generator has exactly `p+2` singleton cycles.  One
exceptional singleton represents one surviving class, while all other
`p+1` singletons represent the second.  Both quotient generators therefore
have support one.  The remaining norm question is whether the relations
identifying the ordinary fibre admit a uniformly bounded local filling; more
prime ranks will not answer it.

The ordinary singleton line now has a uniform matching decoder.  Symbolic
evaluation over `Q(t)` proves that one fixed Wall generator has boundary
`e_t+e_(2-t)`.  The involution has fixed points `1,infinity`, and the exact
four-term chain joins those two.  The resulting matching-difference subspace
has a right inverse of norm exactly `sqrt(2)` for every odd prime.  The live
positive-primary object is reduced to the `(p+1)/2`-dimensional pair-orbit
quotient.  See `TRUE_PROJECTIVE_SINGLETON_MATCHING_DECODER.md`.
This does not contradict the bounded-degree graph no-go: cross-pair parity
demands remain outside the matching section and still require additional
Wall shortcuts or a nonlinear paired-discriminant repair.

The first cross-pair demand has now been solved exactly at the first chart
and bounded at the second.  In the full mod-two HAP boundary, the minimum
support filling of `e_1+e_7` is exactly `11` at `p=3`, while it is at least
`14` at `p=5` (with a verified support-`61` upper bound).  The optimal
eleven-row `p=3` pattern does not specialize to later primes.  This is real
finite-level growth, but not yet an asymptotic obstruction; it directs the
next computation to the symbolic pair-orbit quotient rather than a blind
full-matrix `p=7` solve.  See
`TRUE_PROJECTIVE_PAIR_QUOTIENT_COSET_LEADER.md`.

In fact the strong decoder on **all** cross-pair demands is impossible even
for the full HAP boundary.  Coefficient augmentation detects every ordinary
singleton in a fixed nonzero class of `H_2(SL_3(Z);F_2)`, while the full
`d_3` Tanner graph has uniformly bounded row and column degrees.  Some pair
therefore needs `Omega(log p)` odd source coordinates, forcing every integral
right inverse on all primary boundaries to have norm
`Omega(sqrt(log p))`.  The viable TRUE target is now necessarily the
restricted lattice of primary demands actually produced by the compact
harmonic/carry classes, not a global primary boundary section.  See
`TRUE_BOUNDED_DEGREE_PARITY_DECODER_NO_GO.md`.

That restricted coupling has now been computed exactly at the first two
cuspidal levels.  The compact-to-HAP zero-row identification has difference
rank zero.  At both `p=53` and `p=61`, the two-dimensional harmonic plane has
a rank-one mod-two transgression into the orientation-primary edge sector.
After restoring the two omitted cellular torsion blocks, both harmonic
generators admit exact total HAP cycle lifts.  Thus there is no mod-two
existence obstruction on the actual cuspidal plane at either level.
Moreover, the first compact-to-edge interface now splits uniformly for
**every** finite chart: its free part vanishes by the compact cycle
condition, its torsion part is canceled by the proved norm-one `S_4 -> D_8`
transfer, and its vertical fill is a sum of fixed stabilizer templates.  The
remaining theorem is the next filtration step, where the induced demand
meets positive vertex-stabilizer homology, followed by the integral norm
bound on the paired carry lattice.  See
`TRUE_HARMONIC_PRIMARY_COUPLING.md`.

The same four cuspidal generators now have all-depth two-adic lifts.  Exact
sparse local-ring elimination first produced full corrections at both
`p=53` and `p=61` modulo `2,4,8,16,32,64`; the previous greedy failure at
modulus eight was therefore a choice-of-lift artifact.  Exact rational and
binary ranks, together with the complete discrete-valuation pivot profile,
identify the two-primary correction cokernel at each level as one copy of
`C_4`.  Both harmonic demands have zero free-cokernel component.  Since they
solve modulo eight, their `C_4` components vanish, while multiplication by
two is invertible on the odd torsion.  Consequently both generators solve
modulo `2^k` for every `k>=1` at both charts.  Independent one-CPU MSI reruns
reproduced the exact structure artifacts byte for byte.  This closes
qualitative binary existence at the first two cuspidal levels, not the
family-level metric theorem: neither arbitrary all-depth lifts nor the four
displayed modulus-64 basis profiles bound the minimum operator norm on every
harmonic combination uniformly over the charts.  Generic feasibility search
is obsolete here; the live target is uniform norm control and replication of
the exact local structure across further cuspidal levels.  See
`TRUE_HARMONIC_TWO_ADIC_LIFT.md`.

The restricted modular norm is also exact at these levels.  Enumerating all
three nonzero vectors in each rank-two harmonic parity plane gives section
norms `0.5497745548...` at `p=53` and `0.5389830848...` at `p=61` under
normalized Hamming--Euclidean norms.  In contrast, a fixed cross-pair
singleton demand already needs support `11` at `p=3` and at least `14` at
`p=5`.  The tested harmonic plane therefore avoids the growing coset-leader
signal rather than merely hiding it in the full solver.  This is exact
finite-level evidence, not yet an integral or all-prime theorem.

The next filtration step is nontrivial but now has exact rank.  After one
fixed row-echelon splitting of the solved compact-to-edge interface, neither
harmonic basis vector at `p=53` or `p=61` is directly fillable in the
vertex-resolution row.  Their two classes have rank exactly two modulo
vertex boundaries at both levels.  They form a two-dimensional subspace of
vertex `H_1`, and a homogeneous vertical cycle in the intervening row
cancels that subspace in every computed case.  It is not the separate fixed
two-dimensional `E^infinity` residue in vertex `H_2`.  The live theorem is
therefore a bounded horizontal inverse on this rank-two harmonic image,
then an integral lift compatible with paired carries.  The rank statement
depends on the chosen first-interface splitting and is not an uncancelable
homology obstruction.  See `TRUE_HARMONIC_PRIMARY_COUPLING.md`.

The other stabilizer prime is uniformly harmless in positive degree.  Over
`F_3`, the `D_8` edge stabilizer has no positive homology.  Shapiro and the
projective `S_4` orbit classification show that the vertex `H_2` term is
zero unless `p=1 mod 3`, when it is one fixed `C_3`-orbit coordinate.  Its
integral exponent is three and its support is bounded.  Thus no growing
positive three-primary decoder remains; only the compact harmonic lattice
can carry separate three-primary arithmetic.  See
`TRUE_PROJECTIVE_DERIVED_THREE_PRIMARY.md`.

The next cuspidal chart has now been computed.  At `p=61` the compact
complex is `183<-480<-440<-150`, again with harmonic rank two.  Its cyclic
harmonic discriminant has `114` digits, but its dual systole increases to
`0.3532226523...`, and exact `17`- and `10`-term lifts give a full section
of norm `11.7936523541...`.  Thus the first two cuspidal charts both have
modest free harmonic repair despite enormous discriminant order.  The
observed constant grows, so uniformity remains a theorem rather than an
extrapolation.  See `TRUE_P61_CELLULAR_HARMONIC_SECTION.md`.

The zero-th row of the primary augmentation admits one uniform exact
cancellation.  The first degree-two stabilizer is `S_4`, the degree-one
stabilizer is an index-three `D_8`, and analysis of all thirty actual
subgroups of `S_4` proves that signed torsion transfer is a permutation
isomorphism for every finite coefficient action.  Its inverse has norm one.
This cancels the whole degree-one orientation-torsion block in the zero-th
row; the residual degree-`(3,2)` block and the positive derived stabilizer
rows remain.  See `TRUE_SL3_PRIMARY_TRANSFER_SPLITTING.md`.

`TRUE_NONLINEAR_DISCRIMINANT_REPAIR_FORMULA.md` now gives the exact optimal
nonlinear repair constant, not only a comparison through `Theta`.  It is
the quotient of the ellipsoidal distance to the saturated range lattice by
the lower envelope of the finitely many paired discriminant wells.  This
sharpens the old constants to
`sqrt(Theta^2-1)/||A|| <= C_circ <= Theta/sigma_+`.  More importantly for
the cuspidal chart, it proves
`Q^#=H intersect (Z^m+W)` and embeds
`Q^#/(H intersect Z^m)` into the paired range discriminant.  Hence the
`p=53` regulator, dual systole, and all sub-spherical-threshold paired
classes can be recovered from a two-variable rational lattice pullback;
constructing the full rank-20,000-plus integral cycle kernel is unnecessary.

`TRUE_HARMONIC_INTEGRAL_LIFT_SEQUENCE.md` now converts the remaining
harmonic numerator into an integral decoder.  The spherical annihilator
lattice fits into the exact sequence
`0->L->M_Sigma->Q^#->0`, and the glued range radius is exactly the extra
Pythagorean norm paid by an ambient integer lift.  Its nonlinear lift
distortion is equivalent, in harmonic rank `r`, to the least norm of a
`Z`-linear section up to a rank-only lattice-reduction constant.  For the
rank-two `p=53` chart the factor is `4/sqrt(3)`, and any two integral basis
lifts give a complete bound through a `2 x 2` generalized eigenvalue.  The
same note now gives the exact regulator balance
`Reg(Q^#)=Reg(S_sat)/Reg(L)`.  Thus the harmonic regulator and the
determinant lower bound
`kappa^2>=(3/16)Reg(L)/Reg(S_sat)` at rank two require only saturated
boundary/coboundary determinants and Smith indices, not an exact harmonic
basis.  The basis is still needed for shape, dual systole, and an upper
bound.  At `p=53` the two affine lift problems give a section of norm
`7.49017741972933`, within `0.015%` of the exact shortest-class lower bound;
at `p=61` they give `11.793652354043665`.  The next exact computation should
transport these certificates through the derived bounded-primary
augmentation and test further cuspidal levels; it should not enumerate a
full discriminant group.

The fixed-chart nonlinear optimization is now finite and exact.  By
`TRUE_FINITE_PAIRED_DISCRIMINANT_CERTIFICATE.md`, only finitely many range
lattice sites and paired discriminant wells can be active on a fundamental
polytope.  Their common Voronoi refinement is a finite rational polyhedral
complex, and `C_circ(A)^2<=T` is equivalent to one rational quadratic
nonpositivity test on each cell.  Thus every fixed-chart constant is a real
algebraic number with an exact certificate.  The remaining issue is wholly
uniform: construct one bound for these finite certificates over the
selected chart family.

The compact-model comparison now has an exact quantitative theorem as well.
`TRUE_CHAIN_COMPARISON_DECODER_TRANSFER.md` proves that integral cochain
maps in both directions which induce inverse maps on the harmonic lattice
transport the lift sequence and every integral decoder.  Both the optimal
nonlinear lift distortion and the least section norm change by at most
`||f^2|| ||g^2||`; the chain-homotopy norms do not enter.  Therefore the
level-`53` AGG--HAP comparison may transport two compact-model integral
lifts directly, without reconstructing the full rational HAP harmonic
plane.  At family level, a bounded-propagation integral comparison preserves
uniform decoder bounds.

For fixed free `Z[G]` resolutions, that bounded comparison is automatic.
`TRUE_FIXED_RESOLUTION_DECODER_INVARIANCE.md` uses fixed group-ring
comparison matrices and coefficient-`l1` Schur bounds to obtain one norm
constant for every finite chart.  The modular-symbol/well-rounded cellular
model becomes a fixed projective resolution after inverting its finite cell
stabilizer orders.  Hence its comparison to HAP is uniformly bounded over
the projective family, and the only unresolved change-of-model issue is a
bounded-primary integral correction (notably the two-primary sector), not a
growing real chain-map norm.

On the FALSE side, the paired carry energy now has the coordinate-order
formula in `FALSE_CARRY_MEAN_SUPPORT_FORMULA.md`: its uniform subgroup mean
is a sum of `nu(o_j)` over ambient carry characters, with every nontrivial
coordinate contributing between `2/27` and `1/8`.  This immediately kills
uniform mean pruning for nonzero deck-invariant codes in regular covers of
a fixed presentation, since their support contains a full deck orbit; see
`FALSE_REGULAR_COVER_MEAN_ENERGY_NO_GO.md`.  The exact nonuniform replacement
is `FALSE_BERNOULLI_CARRY_INCIDENCE.md`: in a two-torsion parametrization,
FALSE follows if the maximum carry-row degree `a_n` is negligible compared
with the marked-word row degree `b_n` on a positive fraction of word
coordinates.  The live finite search is therefore an incidence-separation
calculation, not a uniform discriminant average.

Bounded spherical templates already localize every vanishing denominator.
If their maximum norm is `B`, then a dual cycle `u` with `||u||<1/B` pairs
by an integer of magnitude less than one with every template, hence is
orthogonal to the whole spherical lattice.  Its real component therefore
lies in `H_2(H,R)`.  In particular, when a chart stabilizer is rationally
two-acyclic, every nonzero discriminant class has cycle radius at least
`1/B`, uniformly.  This does not bound the paired range radius: the two
remaining failure modes are now denominator collapse inside stabilizer
homology and numerator growth with denominator bounded below.

This also fixes the architecture of the autonomous FALSE solver.  It must
not enumerate exact RF vertex representations and hope that ILP plus an
intertwiner retains the radical sign: `FALSE_RF_VERTEX_HS_MATCHING_NO_GO.md`
proves that every such asymptotically compatible exact-vertex sequence kills
the sign.  The primal variables must include a genuinely nonliftable
normalized-HS almost-representation inside at least one vertex.  Exact RF
models may serve as controls or auxiliary blocks, never as the complete
projective-sector ansatz.

The radius-ten atlas boundary appeared to have a smaller structured ansatz.  With
`H=GL_3(F_2)<A8`, left-coset coordinates give
`ell^2(A8)=ell^2(H) tensor C^120`; relative unitaries
`U_V=(I_H tensor V)J`, `V in U(120)`, preserve exact commutation with the
whole left `H`.  The exact word-support audit kills it: 210 of the 234
failing words lie in `H*H`, forcing a regular commutator defect `sqrt(2)`
for every `V`.  Do not launch this `U(120)` optimization.  Any successful
deformation must break exact `H`-equivariance as well as leave the monomial
category; a dense `U(20160)` search is still not justified.

There is a viable smaller replacement.  Among the 30 point/hyperplane
stabilizers `M` of order 1,344, 18 contain none of the 234 boundary words in
both factors.  For these index-15 subgroups, search
`U_V=(I_(ell^2 M) tensor V)J` with only `V in U(15)`.  This stays in the
full 20,160-dimensional regular sector but evades the exact support no-go.
Implement traces through induced/coset coordinates; do not materialize
20,160-square matrices.

That implicit implementation is now live.  Two bounded orthogonal searches
from rotation scales `0.02` and `0.20` descended toward, but not below, the
balanced tensor-flip loss one.  Stop multiseed optimization.  Compute the
exact induced-coordinate Hessian at `V=I`; a rational positive certificate
would establish local rigidity of every surviving index-15 stabilizer
ansatz, while a negative eigendirection would give a principled continuation
seed.

The exact Clifford word has now been closed algebraically.  Abstract
centrality first gives `c_01=c_02=c_12=q^2` and `q^4=1`.  The local generators
admit the common six-leaf scalar refinement

`D=(000,001,010,011,10,11)`, `G_D ~= GL_6(F_2)`.

This group is superperfect, so its unique lift to the central atlas cover
shows that the common commutator is trivial and `q^2=1`.  Uniformly refining
the second chart gives a superperfect `GL_8(F_2)` chart.  Its overlap with the
six-leaf chart contains the common perfect subgroup

`GL({000,001,10,11},F_2) ~= GL_4(F_2) ~= A8`,

and the element `b` lies in this overlap.  Uniqueness over the two
superperfect charts and agreement over the perfect overlap force their lifts
of `b` to coincide.  Hence the residual discrepancy is trivial and `q=1` in
`P/[P,R]`.  The entire Clifford block is therefore a proved no-go; do not
optimize either its `q=-i` or `q=-1` sector further.  A new FALSE witness must
use another cross-chart relation that survives this perfect-overlap test.
The five-term sequence alone only makes the central kernel a quotient of
`H_2(Q,Z)`, because `H_2(A8*A8,Z)=C2 directSum C2`; it is not automatically
the whole Schur multiplier.  Full proof:
`notes/FALSE_CLIFFORD_TORSION_GATE.md`.

The 64-dimensional block is now executable.  It validates the Pauli
identities below `5.4e-14` and centralizes 19 of the 234 radius-ten boundary
words, all inside one 25-word `(1,b)` projection class.  Six words with the
same projections remain, showing computationally that projection pairs do
not determine compatibility.  A 20-step search over the exact
Clifford-preserving `U(32) x U(32)` manifold lowers RMS slightly but leaves
maximum defect exactly `2`.  The perfect-overlap bridge decides the algebraic
survival problem negatively, so stop numerical refinement of this branch.

The perfect-overlap mechanism has now been run on the entire first boundary.
Among its 234 tensor-flip failures, 178 are proved trivial in `R/[P,R]` by
common superperfect charts of sizes 6, 8, or 10.  The remaining 56 words fall
into only eight projection classes.  They are not merely beyond the search
cutoff: their matrix-support equalities turn the two common-refinement suffix
cardinality equations into positive contradictions, so none can lie in one
scalar chart at any depth.  Their two factor subgroups have orders 4 and 8.
Use one representative from each class for exact central-phase/character
analysis before launching another unitary optimizer.  Full criterion and
counts: `notes/FALSE_ATLAS_PERFECT_OVERLAP_SCAN.md`.

The first of those eight incompatible classes already has an exact phase
seed.  With `a=I+E_10`, `b=I+E_01`, `c=I+E_12`, and
`d=I+E_01+E_12=cb`, the relation

`r=a_2 b_1 c_2 b_1 a_2 b_1 c_2 d_1`

is the identity in the Leavitt group but forces a suffix code to equal its
own proper refinement, so no single scalar chart contains its letters.  Its
local factor groups are `V4` and `D8`.  The Pauli assignment
`b->X`, `c->Z`, `a_2,c_2->cos(pi/8)X+sin(pi/8)Y` gives `r->i`.
Inside the 64-dimensional `(5,2,1)` `A8` irrep, exact restriction characters
give sixteen copies of this two-dimensional block.  Two honest `A8` charts
can therefore be aligned so that `r` has spectrum
`i^[32],1^[16],(-1)^[16]`, commutes with the local `D8` and `V4`, and has
normalized distance squared `2` from one.  It does not yet centralize the
full charts or prove that `r` survives in `R/[P,R]`.  This is now the first
live self-similarity phase seed; full calculation:
`notes/FALSE_SELF_SIMILARITY_PHASE_SEED.md`.

The 64-dimensional seed is now executable rather than character-theoretic
only. Exhausting all six complementary `D8`-character matchings reproduces
the spectrum `i^[32],1^[16],(-1)^[16]`, trace `i/2`, and exact local
centrality to below `1.3e-14`. Every matching nevertheless has full-chart
maximum commutator defect exactly `5/4`; the best twelve-generator RMS is
`0.8228507358`. Thus discrete complement reassignment is exhausted. Continue
only with a genuinely deformable relative-unitary or nonorthogonally coupled
ansatz that trades full-chart centrality against macroscopic phase. Exact
construction and diagnostics: `experiments/atlas_self_similarity_block.py`
and `notes/FALSE_SELF_SIMILARITY_PHASE_SEED.md`.

The full relative-unitary continuation is now the leading FALSE signal.
Starting from the lowest-RMS exact complement, worst-tail Cayley descent in
`U(64)` reduced the maximum of all twelve chart-centrality defects from
`1.25` to `0.0295801`, while moving the normalized relation trace from `i/2`
to `2.4e-9 + 0.9998817 i`. The retained state has
`||r-iI||_2=0.0153837` and operator-norm error `0.0423631`; its alignment is
dense and lies normalized-HS distance `0.78677` from the seed. Stop broad
weight/seed sweeps. The live exact target is now the fixed-dimensional
equation `r(U)=iI_64`: compute its tangent rank, apply a local exact/Newton
solver, and recognize an algebraic block model. Solving it certifies the
one-relator central phase but does not yet prove survival in `R/[P,R]`, where
commutators involving all other Leavitt relators also matter. The
multi-relator central-kernel and negative-corner gates remain. Full record:
`experiments/atlas_self_similarity_refine_results.md`.

Local solvers sharpen that signal but also expose the next mathematical gate.
Repeated PyTorch L-BFGS and an independent matrix-free Gauss--Newton/LSMR
solver reached `||r-iI||_2 = 1.11046e-4` and operator error `2.82906e-4`.
The Jacobian adjoint check is accurate to `1.2e-16`, but all deep Krylov solves
hit their iteration caps, so stop numerical polishing. Algebraically, with
`A=rho_U(a_2)`, `E=rho_U(c_2)`, and fixed `B=rho(b_1)`, `C=rho(c_1)`, the
equation reduces exactly to `(BABE)^2=iC`. Here `A,E` are commuting
involutions with four 16-dimensional joint eigenspaces. Attack this finite
square-root factorization by spectral projectors and character matching; it
is now higher yield than further continuous descent. Details and solver
records: `experiments/atlas_self_similarity_refine_results.md`.

The multiplicities compress once more: the 64-dimensional restrictions are
eight copies of a canonical 8-dimensional package, namely `2*tau` plus the
four linear `D8` characters versus two copies of every `V4` character. Hence
an exact `U(8)` solution of `(BABE)^2=iC` amplifies to the observed 64D model.
`experiments/atlas_self_similarity_block8_search.py` instantiates this
minimal package; its exact recognition is recorded below.

That block-eight search has succeeded and been made exact. In the canonical
block let `S=(0 7)(1 6)(2 5)(3 4)`,
`P=(0 6)(2 4)(3 5)(1 7)`, `F=(I+iC)/sqrt(2)`, `A=BPB`, and `E=PSF`.
Then `A,E` are commuting self-adjoint involutions, all four joint eigenspaces
have dimension two, and `BABE=SF` with `(SF)^2=iC`. Thus the survivor relation
is exactly `i I_8`, and eightfold amplification gives `i I_64` inside the two
honest `A8` charts. Sage verifies the identities exactly over `Q(zeta_8)` in
`experiments/atlas_self_similarity_block8_exact.py`. The one-relator phase
gate is complete; stop optimizing it. The remaining algebraic gate is whether
this class survives after centralizing *all* Leavitt relators, i.e. in
`R/[P,R]`, followed by the negative-corner construction. Full proof:
`notes/FALSE_SELF_SIMILARITY_PHASE_SEED.md` and
`experiments/atlas_self_similarity_refine_results.md`.

The complete radius-ten audit prevents overinterpreting that theorem. The
eightfold exact alignment makes exactly fourteen of the 234 boundary words
scalar, namely the whole conjugacy/inversion class `C_11`; they are `+/- iI`
to below `5.4e-15`. None of the other 220 words is scalar and none of the 178
perfect-overlap-certified zero words maps to identity. The remaining maximum
centrality defect is `1.7375382832`, with boundary RMS `1.4149416221`. Thus
the model does not factor through `P/[P,R]`. The next finite solver must force
representatives of the 24 certified-zero classes to identity while retaining
the exact `C_11` phase, then use the incompatibility pattern for multiplicity
coupling or a multi-chart filling proof. Full audit:
`experiments/atlas_self_similarity_global_audit.py` and
`experiments/atlas_self_similarity_global_audit_results.md`.

The four persistent worst classes near the exact phase do not themselves
give an algebraic obstruction.  All of indices `70,86,90,91` and phase class
`11` lie in a local `S4*S4`.  After imposing the four zero words, this local
presentation has a quotient of order `168` (the degree-eight `PSL(2,7)`)
where class `11` is a nontrivial involution.  Hence no proof using only those
four relations plus the local `S4` laws can kill the phase.  The finite
certificate cannot extend to the ambient simple `A8` factors, so the next
exact target is to exploit certified-zero words outside the local slice to
force ambient-chart extension.  Full proof and audit:
`notes/FALSE_ATLAS_STUBBORN_S4_QUOTIENT.md` and
`experiments/atlas_stubborn_s4_certificate.py`.

The ambient-extension escape is real, not merely local.  The 178
perfect-overlap-certified zero words reduce to 24 cyclic classes.  Exhausting
all `40,320` automorphisms between the two full `A8` factors finds 14 inner
and 12 outer alignments killing all 24 representatives.  Eight inner and all
12 outer solutions keep class `11` nontrivial; an explicit outer solution
maps it to an involution.  Hence class `11` is not in the normal closure of
the entire currently certified package.  This still does not prove survival
in `R/[P,R]`, because the finite `A8` image of class `11` is not central.
The next finite quotient search must impose phase centrality, or a larger
exact atlas scan must find new zero relators eliminating all 20 witnesses.
Full theorem and exhaustive certificate:
`notes/FALSE_ATLAS_CERTIFIED_A8_QUOTIENT.md` and
`experiments/atlas_certified_a8_alignment.py`.

Centrality does not rescue the local four-class obstruction. The central
quotient of the local `S4*S4` presentation maps onto the perfect group
`PerfectGroup(2688,2) ~= (C2^4):PSL(3,2)`, whose center has order two. Both
local `S4` factors embed, the four zero classes map to one, and class `11`
maps to the central involution. The negative central eigenspace of the
regular representation restricts as `56 lambda_S4`; amplifying 15 times
matches `lambda_A8|S4 = 840 lambda_S4`. Hence two honest regular `A8` charts
in dimension `20160` satisfy all four zeros exactly and send class `11` to
`-I`. At that stage this showed that a local obstruction had to use at least
one of the other 20 certified classes.  The later dual-number quotient kills
all 24 certified classes at once and supersedes this intermediate boundary.
Full exact proof and permutation certificate:
`notes/FALSE_ATLAS_LOCAL_CENTRAL_PHASE.md` and
`experiments/atlas_stubborn_s4_certificate.py`.

The simultaneous 24-class solver now gives a first finite compatibility
answer.  With the two `(5,2,1)` `A8` charts fixed, `U(64)` reaches certified
zero-class RMS `1.279437` while retaining the survivor phase to HS error
`0.008520`.  A symmetry-broken full `U(128)` multiplicity-two search reaches
`1.271406` at phase error `0.008401`; its off-block HS mass is `0.334236`, so
the small improvement is genuine rather than a duplicated block.  Zero-only
searches plateau near RMS `0.65` and erase the phase.  Stop broad weight/seed
sweeps in this ansatz.  The preceding finite quotient rules out an exact
obstruction from the four persistent local classes alone.  Add relations
outside their `S4*S4` slice to force ambient-chart extension, or enlarge the
actual vertex irrep multiplicities.  Full scoped result:
`experiments/atlas_self_similarity_multirelator_results.md`.

The exact outer quotient yields a stronger continuous bridge.  The
outer-stable 128-dimensional representation
`rho directSum (rho after theta)` has an alignment which kills all 24
certified classes to `6.5e-15`.  After symmetry breaking, the central target
`-I` gives a new balanced point: zero RMS `0.352252`, zero maximum `0.555910`,
phase HS `0.212666`, phase operator `0.412192`, and phase trace `-0.977386`.
At phase weight ten the phase improves to HS `0.057228` and operator
`0.115708` with zero RMS `0.491114`.  This is decisively better than the `iI`
front.  Multiplicity two does not scale: a symmetry-broken full `U(256)` run
improves the balanced weighted objective by only `0.205%`, with errors still
`(0.352035,0.212209)`.  Stop this fixed outer-pair family and additional
same-dimensional `iI` seeds.  Change the actual vertex irrep content.  Details:
`experiments/atlas_self_similarity_multirelator_results.md`.

Explicitly adding all twelve phase commutators to the exact 30-dimensional
outer-tangent model does not produce a nonlinear central phase.  A
kernel-directed start at weight one ends with all-identity RMS `0.480563`,
maximum `1.368373`, and phase HS `1.366428`; weights `0.1` and `10` remain on
the same two finite-quotient strata.  The exact 136-dimensional tangent kernel
and phase rank 60 are first-order information only.  Stop generic `U(30)`
L-BFGS.  This historically suggested second-order kernel equations or a
coupling of the order-2688 block to the 20 outside classes.  The later
dual-number quotient performs the latter coupling exactly; the surviving
gate is now the four-class central boundary recorded at the top of this
agenda.  Full numerical scope:
`experiments/atlas_self_similarity_multirelator_results.md`.


Free-product conjugacy reduces the 56 apparent survivors further. After
exact cyclic reduction, they form four classes up to conjugacy and inversion,
each of size fourteen, represented by collision-tree indices
11, 30, 44, and 55. All representatives have cyclically reduced length
eight, and none is conjugate to its inverse. Since conjugacy is trivial and
inversion is negation in \(R/[P,R]\), the entire first-boundary package is
generated up to sign by at most these four central classes. Work with these
four representatives, not the eight projection pairs. Reproducible exact
classification and proof are in FALSE_SELF_SIMILARITY_PHASE_SEED.md and
experiments/atlas_survivor_conjugacy.py.

The first genuinely multi-chart filling closure is also exact.  The 178
known perfect-overlap relators collapse to 24 cyclic classes.  Repeatedly
attaching arbitrary cyclic conjugates of those chart cells while keeping the
cyclic boundary length at most eight reaches a fixed point after six cells:
the layer counts are `24,222,462,480,148,22`, for 1,358 classes total, and
none of the four survivor representatives occurs.  Thus every filling which
admits this cyclic attachment ordering must cross intermediate boundary
length at least ten.  At width ten, 13,234 classes occur through three cells;
reverse layers of 292 and 5,200 tagged classes exclude every
cyclic-attachment filling of area at most five.  This is a width barrier, not
nontriviality in `R/[P,R]`; larger
boundaries, nonshellable diagrams, or new chart cells remain live.  Exact
search and proof scope:
`experiments/atlas_survivor_chart_filling.py` and
`notes/FALSE_ATLAS_CHART_FILLING_WIDTH.md`.

The obvious nonorthogonal interpolation between the complementary exact
endpoints is also closed.  For tensor flip `J` and the unique wall alignment
`L_k`, the relative permutation has `(J^*L_k)^4=1`, so there are only eight
square-root branches up to scalar.  A balanced implicit regular-space scan
gave boundary mean projective loss at least `0.9937`, wall-failure mean at
least `0.9676`, and shared-control mean at least `0.8301` for every branch.
Do not run more branches or seeds in this one-operator functional calculus.
Full signal: `experiments/atlas_boundary_geodesic_results.md`.

The natural enlargement of the genuine prefix-swap symmetry is exhausted as
well.  Every two-sided coordinate twist has the form `w_M=M_2 v`; it still
exchanges the two atlas factors exactly when
`M_2 in K_2 intersect N_Q(K_1)`.  Exact enumeration of all 20,160 matrices,
with Leavitt chart membership decided over `F_2`, gives

`K_2 intersect N_Q(K_1)={1}`.

Thus this whole family acts only by the already-known
`11 <-> 55`, `30 <-> 44` swap and cannot identify the final two central
classes or make either self-inverse.  This does not compute the full Leavitt
normalizer or rule out unrelated inner symmetries.  Exact proof and audit:
`notes/FALSE_ATLAS_TWISTED_SWAP_NO_GO.md` and
`experiments/atlas_twisted_swap_normalizer.py`.

The original square-zero paired class with stable letter inside `Q` is
invisible in every finite coefficient-ring quotient.  Each Laurent inverse
becomes a positive power of a finite-order unit, so the positive and Laurent
ring images coincide; the original Baumslag--Solitar subgroup then acts
trivially on the finite coset set and its augmentation transgression
vanishes.  Do not sweep finite ring quotients for that internal-stable-letter
model.  The stronger construction in
`FALSE_RADICAL_BS_PAIRED_KUN_THOM_DOUBLE.md` escapes the no-go by taking
`c=(c_0,s)` with nontrivial external substitution projection.  Its finite
`L`-coset incidence is now a live quantitative FALSE target.  Precise scope:
`notes/FALSE_SQUARE_ZERO_FINITE_RING_QUOTIENT_NO_GO.md`.

The fold-aligned class has an exact finite-quotient dichotomy.  In the
natural coefficient-ring quotients, `h` acts trivially on the `L`-coset set
and `c` acts by the transvection `s=I+e_13`.  If its cycle length is `M`,
the orbit-stabilizer map on `H_2(-,F_p)` is multiplication by `M`.
Therefore the paired augmentation class vanishes when `p` does not divide
`M` and survives on every orbit when `p|M`.  For
`SL_d(Z/MZ)`, `s` has order exactly `M`.  Restrict the quantitative search
to `p`-divisible moduli and compute the Fourier-symbol carry/marked ratio on
one cyclic block; arbitrary finite-quotient sweeps are obsolete.  Full
chain formula and proof:
`notes/FALSE_RADICAL_BS_FINITE_CYCLE_TRANSGRESSION.md`.

The integral group behind that transgression is also exact:
`H_1(B,I_M)=Z/N_MZ` with `N_M=((p+1)^M-1)/p`, and the displayed paired
cycle is a generator.  For `M=p^k` its primary order is exactly `p^k`.
The natural primitive clock has one small distinguished increment, while
its translated increments have mean zero and squared chordal energy exactly
two.  The latter quantity is not a Baumslag--Solitar relator defect: for the
two exact sectors `H_k,H_k^(p+1)` it is precisely the marked fold energy,
and the local BS relations have zero defect.  The clock also extends exactly
over the full finite coefficient `SL_3` orbit.  Left regular coefficient
covariance and a commuting right clock translation retain squared fold
displacement two.

The abstract external group is now exact as well.  At depth `k`, the clock
element in `SL_3(Z/p^(k+1)Z)` and the distinguished transvection in
`SL_d(Z/p^k Z)` both have order `p^k`.  An explicit gauge on the principal
bundle
`SL_3(Z/p^(k+1)Z) times SL_d(Z/p^k Z)` therefore gives two honest external
representations: the untwisted action and one in which the transvection has
the prescribed right-clock factor.  Every `Q times L` relation and
cross-commutator is exact, while the fold remains macroscopic.  Thus generic
external-unitary optimization is obsolete.  The remaining FALSE gate is
the simultaneous Laurent-tangent/base-elementary covariance and agreement
on the fixed positive polynomial window.  Its finite input is now the
explicit principal-bundle cocycle, not an arbitrary matrix family.  See
`FALSE_RADICAL_BS_INTEGRAL_CYCLE_AMPLIFIER.md`,
`FALSE_RADICAL_BS_Q_BIMODULE_EXTENSION.md`, and
`FALSE_PAIRED_FOURIER_PRINCIPAL_BUNDLE_SPLICE.md` and
`FALSE_EXACT_PRINCIPAL_BUNDLE_EXTERNAL_COMPLETION.md`.

The paired Fourier cell is functorial on finite tangent modules.  For any
finite abelian module with a perfect duality and any finite group acting on
it, translation and multiplier representations on the regular orbit are
exchanged by Fourier transform, while one right gauge fixes all translations
and scales all multipliers by `1+p`.  Taking the acting finite group to
include both the coefficient `Q` quotient and the finite base elementary
group makes every base conjugation and coefficient covariance relation exact
automatically.  Thus the remaining full-vertex problem no longer includes
separate base-matrix optimization: it is to construct one sequence of finite
Frobenius tangent modules carrying compatible positive and Laurent window
maps, with vanishing prefix-bad rank.  The fixed-base square-zero jet rings
give local candidates, but their simultaneous incidence/fusion theorem is
still open.  See `FALSE_PAIRED_FOURIER_FINITE_MODULE_FUNCTOR.md`.

There is a necessary quantitative warning for combining that cell with the
exact external principal bundle.  In an `M`-level cyclic polarization, the
second compressor accumulates one `q^(-1)` shear after each complete cycle:
`Ad(S_1^M)B_1(z)=B_1(q^(-1)z)`.  If `q` has order `r` on the marked tangent
module, then the projective order of `S_1` is divisible by `Mr`.  The naive
coinduced exact bundle consequently has common-positive agreement density
only `1/r`; for the primitive `p^n` clock its squared HS discrepancy is
`2(1-p^(-(n-1)))`, independently of `M`.  Thus long-chain completion and
exact external completion cannot simply be tensored or coinduced.  The live
finite target is a holonomy-canceling multi-chain incidence code, or a
genuinely nonconstant solution of the fiber equation `(LFE29)`.  See
`FALSE_LONG_CHAIN_BUNDLE_MONODROMY_NO_GO.md`.

A balanced scalar wall code on one cycle does not evade this obstruction.
If `y_j` is its accumulated shear and `s_j=y_(j+1)-y_j` its wall increment,
then `|supp(s)|<=2|supp(y)|`.  More generally
`|supp(dy)|<=Delta|supp(y)|` on a graph of maximum degree `Delta`.  Hence a
bounded-degree scalar coboundary cannot have vanishing positive mismatch
and macroscopic marked energy.  Any computational wall search must build
growing marked incidence, moving local commutants, or higher/nonabelian
derived data rather than merely adding a distant compensating wall.

The central-relator endpoint has an exact cocycle linearization.  For a
finite quotient `Q` of the presented radical double and modulus `m`, every
cyclic central extension with chosen generator lifts is a normalized
`2`-cocycle plus `d` lift phases.  Relator and marked-word exponents form
the image of one linear map
`Z^2(Q,Z/m) directSum (Z/m)^d ->(Z/m)^(ell+1)`.  Once
that image is computed, the finite FALSE test is a fixed-dimensional
modular closest-vector/MILP problem: make the first `ell` circular
coordinates microscopic while the last stays macroscopic.  This replaces
finite multiplication-table synthesis and all unitary optimization by
proof-producing finite cohomology.  See
`FALSE_CENTRAL_RELATOR_COCYCLE_LINEARIZATION.md` and
`FALSE_CENTRAL_RELATOR_SEPARATION_CRITERION.md`.

There is an even smaller free-part test, but it is now closed.  For a finite quotient
`F_d->Q` killing the marked radical word, put
`M_Q=ker(F_d->Q)/[F_d,ker(F_d->Q)]`.  Lift-equipped cyclic central
extensions of `Q` are exactly finite characters of `M_Q`; relator and word
curvatures are their evaluations on `[r_j]` and `[w]`.  Radicality forces
`[w]` to lie in the integral span of the defining-relator classes for each
fixed `Q`.  If the real `l_1` filling norm
`min{sum|c_j|:[w]=sum c_j[r_j] in M_Q tensor R}` were to tend to infinity,
LP duality would construct rational characters with marked phase exactly
`-1` and relator defects at most `pi/D_Q`.  However the five-term exact
sequence gives `M_Q tensor R ~= H_1(F;R)=R^d`, carrying every word to its
exponent-sum vector.  Therefore `D_Q` is the same finite abelianized
presentation constant for every finite `Q`; it cannot diverge.  The remaining
central search is purely torsion/modular: compute the marked and relator
classes in `M_Q/mM_Q`, not rational LPs.  See
`FALSE_FINITE_QUOTIENT_RELATION_FILLING_CRITERION.md` and
`FALSE_REAL_RELATION_FILLING_NO_GO.md`.

The surviving torsion target has a smaller intrinsic form.  For a finite
quotient `F_d->Q` with kernel `L`, the five-term sequence splits
noncanonically as

`L/[F_d,L] ~= H_2(Q;Z) directSum K_Q`,

where `K_Q=ker(Z^d->Q_ab)` is free of rank `d`.  Fix one integral exponent-
sum filling `epsilon(w)=sum c_j epsilon(r_j)`.  Then

`kappa_Q=[w]-sum c_j[r_j]`

is the Hopf class of `w product r_j^(-c_j)` in `H_2(Q;Z)`.  Any successful
central certificate must detect `kappa_Q` macroscopically; the fixed free
lattice filling cannot amplify vanishing relator phases.  Therefore screen
finite quotients by the marked Schur class first, then solve only the
prime-power character problem in `H_2(Q)/m` plus `d` lattice coordinates.
See `FALSE_SCHUR_MULTIPLIER_MARKED_REDUCTION.md`.

The MSI Schur pipeline has passed one exact repository-level validation.  For
the local atlas perfect central extension `E=PerfectGroup(2688,2)`, its center
has order two, the base `E/Z(E)` has order `1344` and is perfect, and HAP
computes

`H_2(E/Z(E);Z)=C_2 directSum C_2`.

Since `E` is perfect, its central `C_2` extension is nonsplit and therefore
occupies a nonzero Schur class.  This does not prove FALSE because the atlas
phase is not a certified radical word; it verifies the exact computation and
the central-to-Schur interface before applying it to the Kun--Thom marked
class.  See `experiments/atlas_schur_multiplier_validation_results.md`.

The local growing-curvature existence problem is now explicit as well.  For
`M=p^k`, `n=p^(k+1)`, take

`B_k=C_n semidirect_(1+p) C_M`

and the finite augmentation module

`J_k=Aug_(Z/n)(B_k/<h>)`.

The split LHS sequence and the integral clock Smith calculation give a
literal subgroup `C_(p^k)<=H_1(B_k,J_k)`.  Hence the finite split group

`G_k=J_k semidirect B_k`

has Schur-multiplier exponent divisible by `p^k`.  Thus unbounded finite
Schur curvature is not merely possible in an abstract module: it occurs in
one closed-form finite group family.  The unresolved gates are relative—map
this class into a quotient of the full Kun--Thom vertex, kill its restriction
to the positive edge group, and choose the finite presentation gauge with
vanishing relator phases.  See
`FALSE_SPLIT_SQUARE_ZERO_H2_AMPLIFIER.md`, Theorem 5.

The first exact instance has been checked on MSI.  For `p=3,k=1`, GAP
converts the four-generator presentation of `G_1` to a pc group of order
`2187` and computes

`H_2(G_1;Z)=C_3 directSum C_3 directSum C_9`.

The multiplier exponent is `9`, stronger than the theorem's required lower
bound `3`.  This validates the finite reduction and the Schur computation;
it does not address the relative positive-edge restriction.  See
`experiments/split_clock_schur_k1_results.md`.

The growing local Schur class now has an explicit cocycle, not merely an
order certificate.  On `J_k=Aug_(Z/p^(k+1))(C_(p^k))`, define

`lambda_k(x)=sum_j x_j(1+p)^(-j) mod p^(k+1)`.

The crossed homomorphism on
`B_k=C_(p^(k+1)) semidirect C_(p^k)` given by

`alpha_k(h)=lambda_k`, `alpha_k(c)=0`

is well defined, and

`omega_k((x,g),(y,t))=alpha_k(g)(g.y)`

is a normalized `2`-cocycle on `G_k=J_k semidirect B_k`.  Its exact order
is `p^k`, detected by
`lambda_k(e_0-e_1)=1-(1+p)^(-1)`.  This is the form needed for computation:
globalize one explicit modular formula and evaluate it on the fixed vertex
relators.  See `FALSE_SPLIT_CLOCK_EXPLICIT_COCYCLE.md`.

The apparent final `2d` same-model gauge problem is closed for the actual
Kun--Thom word.  With two scalar generator gauges, an edge word `u` has
discrepancy `q^(epsilon(u))` and the marked element has discrepancy
`q^(epsilon(h))`.  But `h=t^(-1) gamma t` with `gamma in Gamma`, so

`epsilon(h)=epsilon(gamma)`.

The marked displacement is exactly an edge discrepancy and tends to zero
whenever the amalgam relations do.  More generally it is bounded by a fixed
telescoping combination whenever `epsilon(h)` lies in the integral span of
edge exponent vectors.  Do not optimize this scalar ansatz.  The live object
is a genuinely relative multiplier: two vertex Schur classes with equal edge
restriction but nonzero fold difference, equivalently a class in the kernel
of vertex-to-edge restriction.  See
`FALSE_FOLDED_DOUBLE_SAME_MODEL_NO_GO.md`.

The explicit finite clock is also absorbed by the exact relative Shapiro quotient
in every natural finite coefficient-ring image.  There the positive image is
normal and contains `H_k=<h>`.  Since `H_k` acts trivially on `J_k` and
`p^(k+1) J_k=0`,

`H_1(H_k,J_k)=J_k`,

and inclusion into `B_k` followed by the clock projection is the surjection

`J_k -> J_k/(c-(1+p))J_k=C_(p^k)`.

Thus every stabilizer contains a subgroup whose homology already covers the
whole clock coordinate; the relative class is zero at every level.  Do not
run larger Schur computations merely to retest exact survival on this natural
tower.  This does **not** rule out asymptotic branch cutting: the primitive
clock phase on a bounded coordinate is `O(p^-k)`, while the order-`p`
Bockstein shadow has fixed phase.  The finite Laurent translation may equal a
positive word whose length grows with `k`; hyperlinear gluing tests each fixed
positive word, not exact triviality on the whole finite positive image.  The
live natural-tower computation is therefore the centered clock-coordinate
energy of the explicit Shapiro cocycle on the fixed presentation relators,
minimized over Schreier gauges, together with its phase on the growing
collision.  See `FALSE_NATURAL_FINITE_CLOCK_RELATIVE_ABSORPTION.md` and
`FALSE_EXACT_ABSORPTION_BRANCH_CUT_DISTINCTION.md`.

The common-Schur-cover calculation now resolves the residual first-level
image-comparison ambiguity exactly.  At `p=3,k=1`, the ambient multiplier is
`C_3 directSum C_3 directSum C_9`.  The translation-positive and pure-cycle
subgroups have unequal images `C_3 directSum C_9`, intersect in `C_9`, and
together generate the entire ambient multiplier.  Hence their simultaneous
relative cokernel is zero, not the `C_3` seen after either map separately.
This confirms that no exact natural-tower Schur direction was hidden by the
two independent HAP target models.  See
`experiments/split_clock_relative_schur_cover_k1_results.md`.

The local metric part of that distinction is now solved explicitly.  On the
positive subgroup `P_k=J_k times <h>`, first power the primitive central
character by the inverse of the distinguished unit clock coordinate.  The
normalized clock multiplier is then the inflation of the standard Weyl
multiplier on `(Z/p^k)^2`.  A diagonal sparse-seam gauge of width `L|p^k`
makes the two basic squared HS errors at most

`4 pi^2 L^2/p^(2k)` and `4/L`.

Taking `L` near `p^(2k/3)` gives HS error `O(p^(-k/3))` on every fixed
bounded Weyl window, while the `p^(k-1)`-fold commutator remains the fixed
scalar `exp(2 pi i/p)`.  Thus exact positive absorption is locally
asymptotically repairable; no numerical local gauge search is needed.  The
remaining gate is simultaneous equivariance for the other Shapiro/external
transition coordinates.  See `FALSE_CLOCK_POSITIVE_WEYL_SEAM.md`.

The unit normalization is essential: the standard integer representative of
`q^(-1) mod p^k` is not uniformly bounded, so the raw modular formula does
not by itself give a small chord.  After unit normalization the distinguished
coordinate is exactly `1 mod p^k`, making both the vanishing local chord and
the fixed `p`-th-root Bockstein phase invariant statements.

For a nonconstant induced bundle, the seam bound has the scalar form
`R^2 L^2/M^2+A/L`.  Its exact asymptotic criterion includes three conditions,
not only the interior product condition:

`R=o(M)`, `A=o(M)`, and `RA=o(M)`.

The product condition alone fails when one moment vanishes and the other is
linear in `M`; for several fixed generators the three conditions must be
applied to the separate maxima `R_*` and `A_*` so one common seam width
works.  Future Schreier-gauge screens must record all three normalized
statistics.  See `FALSE_INDUCED_WEYL_SEAM_ENDPOINT_AUDIT.md`.

Property `(T)` now closes this scalar seam for the actual primitive
principal bundle.  If `r(tx)=r(x)+1 mod M`, the root-valued vector
`exp(2 pi i r/M)` has mean zero on every transvection orbit.  A Kazhdan
inequality and the chord-to-centered-arc bound give, for some fixed
generator `s`,

`avg_x |r(s^(-1)x)-r(x)|_M >= (kappa^2/(4 pi)) M`.

The RMS moment is also linear.  Hence whichever Weyl transition coordinate
carries this primitive holonomy violates one of the necessary separate
conditions `R=o(M)` or `A=o(M)`, even if the other moment vanishes.  Do not
optimize scalar principal-bundle seams further.  The remaining globalization
must change the tangent/Fourier functor with the base point or use genuinely
higher incidence.  See
`FALSE_PROPERTY_T_PRIMITIVE_HOLONOMY_MOMENT_NO_GO.md`.

This also audits the coherent-Ioana shortcut.  A fixed countable lift with a
finite-stage representative in the integral horocyclic chart would give
bounded transition moments, contradicting the linear Kazhdan lower bound for
the prescribed primitive coordinate.  Hence, for that exact scalar bundle,
the coherent lift, its compatibility with the primitive finite reductions,
and the integral-chart gauge cannot all hold.  The conditional reduction in
`FALSE_IOANA_COHERENT_SCHREIER_LIFT_CRITERION.md` remains valid, but its
sufficient hypothesis is now excluded for the primitive principal-bundle
seam.

The principal-bundle cocycle cannot be ignored by keeping the additive
coefficient character constant over the external quotient.  Write its
clock coordinate as `r_k:SL_d(Z/p^k Z)->Z/p^k Z`, with
`r_k(tx)=r_k(x)+1`.  The root-valued function
`exp(2 pi i r_k/p^k)` has mean zero.  Property `(T)` therefore forces some
fixed external generator to change `r_k` on a positive fraction of points.
Every nonzero change conjugates the primitive-orbit coefficient clock by a
nontrivial power and has squared normalized HS cost at least two.  Hence the
constant coefficient ansatz has a dimension-independent relation-defect
floor.  A successful model must use base-dependent tangent characters to
absorb the exact cocycle, while keeping the two fields asymptotically equal
on the fixed positive polynomial window.  See
`FALSE_PRINCIPAL_BUNDLE_CONSTANT_COEFFICIENT_NO_GO.md`.

The exact paired Fourier--`Q` cell supplies the required escape from that
constant-field no-go on the marked additive window.  On
`ell^2(Q_n times V_n times V_n)`, the common positive module is represented
by translations `A_n(v)`, its Laurent image by multipliers `D_n(v)`, and a
finite Fourier wall exchanges the two.  A right bimodule gauge commutes with
every `A_n(v)` but scales every `D_n(v)` by `1+p`.  Hence the two compressor
choices have identical forward action on the entire common additive module,
while their inverse conjugates of the marked element differ by a fold of
squared normalized HS size two.  All coefficient-`Q_n` covariance is exact.
This is a literal base-dependent tangent twist, not a diagonal clock
reinterpretation.  What remains is to globalize the one cell to a finite
Frobenius model of the full Laurent tangent module and base elementary group,
while coupling the actual external `t,s` substitutions.  See
`FALSE_RADICAL_BS_PAIRED_FOURIER_Q_CELL.md`.

The abstract external group can be attached to that Fourier cell exactly,
not merely through diffuse unitary completion.  The principal-bundle gauge
works for arbitrary finite-order unitary fibers.  Both Fourier-cell
compressors are finite-order Clifford operators: the first has order
dividing eight, while the second is a product of a finite right translation
and finite Heisenberg normalizers.  Choose a congruence modulus divisible by
their orders and prescribe the two commuting transvections on each left
`(Z/mZ)^2`-orbit.  This gives honest external `SL_d` representations with
compressor `S_i` and stable transvection `1`, up to common regular factors.
Thus the marked Fourier cell, its stable-letter identity, and every abstract
external relation are exact simultaneously.  Only covariance for the other
Laurent tangent and base-elementary generators remains.  See
`FALSE_EXACT_PRINCIPAL_BUNDLE_EXTERNAL_COMPLETION.md`.

The cyclic-seed Kazhdan estimate is now known to be intrinsically tracial.
For every finite tracial von Neumann algebra `(M,tau)`, exact covariant
realizations `(rho_i,Phi_i)`, and arbitrary comparison vector
`T in L^2(M,tau)`, one has

```text
||Phi_0(w)T-T Phi_1(w)||_2
 <=C epsilon+2(C+1)eta/kappa,
```

where `C` is the integral orbit-coefficient cost of `w` from the seed,
`epsilon` is the seed discrepancy, and `eta` is the base-intertwining
defect.  The proof is the same Kazhdan projection in the standard form;
finite dimensionality, boundedness of `T`, and Connes embeddability are not
used.  Thus passing from matrices to finite factors or commuting-operator
tracial targets cannot rescue exact-covariance Frobenius mixing.  The live
FALSE gate is genuinely approximate/nonliftable tangent covariance in every
tracial model, not a matrix compactness issue.  See
`FALSE_KAZHDAN_CYCLIC_SEED_TRACIAL_EXTENSION.md`.

The remaining approximate tangent-covariance gate now has an exact finite
Fourier statistic.  For a finite abelian tangent group `W`, subgroup `K`,
two character representations `Phi_i`, and comparison operator `T`,

```text
(1/|K|) sum_(k in K)||Phi_0(k)T-T Phi_1(k)||_2^2
 =2 sum_(chi|K != psi|K)||p_0(chi)T p_1(psi)||_2^2.
```

Thus full-subgroup RMS covariance is exactly twice the mass outside the
correct character-restriction blocks.  In matrices, it bounds the `l^1`
mismatch of the restricted multiplicity vectors; if those multiplicities
agree, the proposed implementer lies within the RMS defect of an exact
unitary `K`-intertwiner.  No root-spacing or exponent loss occurs.  Hence a
live Frobenius model must exhibit a strict local-to-global failure: vanishing
generatorwise covariance but macroscopic covariance defect averaged over
the growing tangent subgroup.  This gives a finite exact diagnostic for the
remaining nonliftable field.  See
`FALSE_FINITE_ABELIAN_COVARIANCE_TWIRL.md`.

There is an unavoidable quantitative boundary to that twirl.  If a finite
abelian group `K` of order `N` is generated by a fixed window of size `m`,
simultaneous pigeonhole approximation in the dual torus gives

```text
eta(K,S)=min_(chi!=1) sum_(s in S)|chi(s)-1|^2
 <=4 pi^2 m/(ceil(N^(1/m))-1)^2
 =O_m(N^(-2/m)).
```

Thus every growing bounded-generator abelian tangent family has collapsing
dual gap.  Combining the finite Cayley Poincare inequality with subgroup
twirling yields the exact fixed-window loss

```text
E_K(T)^2<=Delta_S(T)^2/lambda(K,S).
```

Consequently fixed-window hyperlinear covariance upgrades to an exact
full-subgroup intertwiner only under the extra rate
`Delta_S=o(sqrt(lambda))`.  Hyperlinearity supplies no relation between
defect and the model-dependent output group size, so adaptive
diagonalization does not provide this rate.  Any universal TRUE proof must
use the regular `0/1` trace/prefix structure beyond generic Poincare
rounding.  See `TRUE_FIXED_WINDOW_DUAL_GAP_COLLAPSE.md`.

The long-chain monodromy obstruction now has a genuinely different local
escape.  For every finite field `F_l` and `n>=3`, choose a primitive
degree-`n` polynomial and the distinct primitive polynomial of its inverse
root.  Multiplication by `x` in the two fields `F_(l^n)` gives companion
compressors of the same exact order `l^n-1`.  In their common coefficient
basis the first `n` positive iterates of `1` agree literally, while the two
inverse iterates differ.  The regular Fourier character model therefore has

```text
Ad(U_0^j)Z(1)=Ad(U_1^j)Z(1),  0<=j<n,
||Ad(U_0^-1)Z(1)-Ad(U_1^-1)Z(1)||_2^2=2.
```

Choosing `n` above every intermediate degree also makes the two quotient
fields identical on any prescribed bounded positive polynomial computation.
Unlike the sheared cyclic chain, there is no extra clock-order factor and no
orbitwise density loss.  This solves the local equal-order Frobenius cell;
it does not solve FALSE, because the two recurrence fields still require a
base-dependent, genuinely nonliftable transport under the other external
substitutions.  Exact Kazhdan-covariant completion would again kill the fold.
See `FALSE_PRIMITIVE_RECURRENCE_FROBENIUS_PAIR.md`.

In fact the cell has `phi(l^n-1)/n` sectors: every primitive degree-`n`
recurrence has the same positive arc and compressor order, and every two
inverse Fourier labels have squared HS distance two.  The local alphabet
therefore has unbounded incidence, not merely two branches.

A fixed-constant-term packing argument strengthens this to an exponential
primitive-sector code with linear Hamming distance between inverse
recurrence vectors.  Coordinatewise regular additive characters compress
that distance to dimension `O(n)` while retaining a constant HS fold.  The
remaining missing datum is a low-defect unitary transport for the dense
feedback rows; the coordinate character set is not recurrence-invariant.

That compressed transport is now closed exactly.  If `w(f)` is the number
of nonzero nonconstant feedback coefficients of a primitive recurrence,
the optimal full-additive RMS covariance cost of its coordinate-character
model is

```text
epsilon(f)^2=2(l-1)w(f)/(ln).
```

For two recurrences with the same constant term, their compressed inverse
fold is at most `l/(l-1)` times the sum of these two costs.  Thus linear
inverse-code distance forces constant covariance cost: independent
coordinate transport cannot realize low-carry/high-fold behavior.  Any use
of the recurrence alphabet must couple feedback rows through a genuinely
higher-incidence character construction.

The stabilizer-frame route now has an exact nonabelian Fourier refinement.
For a finite deck subgroup `A`, decompose the canonical real filling as
`q=directSum q_pi` and put
`rho_pi=Tr_(V_pi)(|q_pi><q_pi|)` on the multiplicity space.  Then

```text
||T_(A,q)||_op^2=max_pi (|A|/dim(pi))||rho_pi||_op.
```

Consequently bounded marked ratio forces every fixed amount of filling mass
to occupy linear effective Plancherel capacity
`sum dim(pi) rank(rho_pi)`.  Concentration on sublinear capacity proves
FALSE.  This is sharp: a delta vector in the regular representation has
noninvariant norm tending to one but orbit-frame norm exactly one.  Thus the
bounded-real stabilizer branch has a precise alternative: low-capacity deck
Fourier concentration proves FALSE, while a Plancherel-flat filling leaves
only the nonlinear discriminant/carry obstruction.  See
`FALSE_NONABELIAN_DECK_FRAME_BLOCKS.md`.

For the explicit constant-stabilizer tower, the Kazhdan decoder forces the
flat alternative.  It upgrades from one bounded noninvariant filling to an
equivariant right inverse for the entire deck orbit.  If `T_n` is the marked
analysis operator of all translated minimum real fillings, then

```text
Fill_(R,2)(w;H_n) <= ||T_n||_op
 <= max{Fill_(R,2)(w;H_n),C_J}.
```

Thus the intermediate real fill is the only possible unbounded real mode.
If it is bounded, every nontrivial reduced deck density obeys the uniform
Plancherel-flat estimate
`||rho_(n,pi)||_op<=C_J^2 dim(pi)/|A_n|`; no hidden
low-capacity real sector remains.  Integral filling still diverges in this
branch, so the sole surviving gate is the nonlinear marked
discriminant/carry obstruction.  See
`FALSE_KAZHDAN_ORBIT_FRAME_OPERATOR_BOUND.md`.

The square-level integral-cycle screen has now been corrected from a partial
packet to a full exact packet.  At levels `49,121,169`, primitive integral
two-cycles span all of rational `H_2`; their support maxima are respectively
`11,311,220`, and their coefficient maxima are `2,4,7`.  At `121` and `169`,
the enormous natural-order rows were pivot artifacts: reversing the cellular
coordinate order exposes all seven and all twelve directions with small
integer coefficients.  The natural-order short subpacket ranks `2` and `4`
match the published cuspidal dimensions, while the complementary dimensions
`5` and `8` match the square-level Eisenstein formula; identification still
requires the absolute-to-relative map.  The next family theorem is to explain
the reverse-order filtration symbolically and bound support/synthesis and
integral saturation uniformly.  See
`TRUE_SQUARE_LEVEL_EXACT_CYCLE_PACKETS.md`.

The determinant-one level-`121` packet now has an exact bridge to the dual
integral-carry sequence.  If packet cycles `c_i` project to a `Z`-basis of
`Q`, then

```text
K=S_sat directSum <c_i>_Z.
```

For the packet-dual basis `u_i` of `Q^#`, any primitive cycle basis `B` and
integral right inverse `BR=I` give the dual lifts explicitly by

```text
P_(ij)=<u_i,B_j>,       Z=(R P^T)^T.
```

The rows of `Z` annihilate the saturated boundary lattice, project to the
`u_i`, and form an integral section of
`0 -> L -> M_Sigma -> Q^# -> 0`.  Thus the full rank-seven carry problem is
one exact right-inverse computation, not a nonlinear phase or modular-SAT
problem.  Direct content-normalized unit elimination solves the `632 x 1940`
system for all seven right sides in `0.057s`: `630` unit pivots leave two
rows of contents `2,4`, division exposes the last two unit pivots, and no
residual remains.  Converged greedy range reduction gives an exact integral
section with coefficients at most `2`, lift squared norms
`480,188,67,91,226,6,34`, and

```text
||s_121||<=21.9892802606427564....
```

This is the first full numerator certificate for all seven new level-`121`
directions.  It is an upper bound, not CVP, and the `2,4` residual contents
are presentation-dependent rather than intrinsic Smith invariants.  See
`TRUE_PACKET_TO_DUAL_CARRY_SECTION.md` and
`TRUE_N121_DUAL_CARRY_SECTION.md`.

The exact amenable coadjoint orbit has a uniform compression obstruction.
For any property-`(T)` group `H`, infinite-index subgroup `A`, Kazhdan pair
`(S,kappa)`, and trace-one density operator `rho` on `ell^2(H/A)`,

```text
max_(s in S)||lambda(s)sqrt(rho)-sqrt(rho)lambda(s)||_(HS)>=kappa.
```

Indeed conjugation on Hilbert--Schmidt operators has no invariant vector:
an operator commuting with an infinite transitive permutation action has
constant column norm and hence cannot be nonzero Hilbert--Schmidt.  Applied
to the framed character stabilizer, this proves that direct finite-rank
compression or repetition of its exact induced monomial representation
cannot create normalized-tracial models.  Amenable-stabilizer sofic charts
solve rooted transport only.  The live finite experiment must retain two
external fields and their nonliftable relative holonomy; a one-field orbit
compression is guaranteed to show a Kazhdan defect floor.  See
`FALSE_COADJOINT_INDUCTION_KAZHDAN_TRACE_NO_GO.md`.

## Banked (kernel-checked, this repo)

Theorem A (nonsofic groups exist); the norm–trace interface; the free-lamp
reduction to KT 4.1 (verbatim-pinned); the f.d. collapse (H_K not MAP);
the profinite-closure criteria; the scalar-phase obstruction.  External
pins verified from source: KT 4.1 (arXiv:2608.06222v1), Preusser
(arXiv:1912.11386).  Dead, do not re-attempt: the seven phase-story
routes; exact-stratum ansätze on closure-swallowing frame pairs; the central
free-lamp cover as a counterexample mechanism.  Indeed
`K *_Z (Z × ℤ)` is sofic whenever `K` is sofic by amenable-amalgam closure,
and its central quotient cannot be used because soficity is not known to pass
to arbitrary quotients.  `Sofic/CentralFreeLampCover` deliberately proves no
contrary closure claim.

### 2026-08-12: exact rank-three audit repairs the Leavitt atlas target

The proposed global implication “234 first-boundary relations force the
`GL3(2)` overlap” is false.  Over `F2[A8]`, the left ideal generated by all
signed-prefix derivatives has codimension `155`; the quotient module
produces a finite group

```text
E=(F2[A8]/I) semidirect A8
```

with two injective regular-margin `A8` charts satisfying every boundary word
exactly but disagreeing on four standard generators of `GL3(2)`.  An
independent Boolean functional of support `9408` annihilates all `234*20160`
left-translated derivative rows and pairs to `1` with every bridge, so the
countermodel does not depend on the discovery rank calculation.

Collision word `19243` nevertheless kills every affine deformation over the
fixed classical order-zero fold: its projected centrality commutator is a
fixed nonidentity commutator in `A8`.  Independently, an exhaustive scan of
all `9! = 362880` labeled pairs of natural point-stabilizer `A8` charts in
`A9` finds one boundary survivor (the classical alignment) and no survivor
after adding word `19243`.  The `A10` extension checks all
`10!/2 = 1814400` distinct labeled charts modulo the base-chart centralizer
and gives the same result.  Every different eight-point support in `A10`
already fails the first boundary word.

The live target is therefore classification of all CE regular-margin
solutions of a boundary-plus-interior packet.  Ordinary tracial SOS cannot
provide that classification: the presented atlas group has its exact regular
group-von-Neumann-algebra model, so any positivity identity valid in every
finite tracial algebra would also hold there.  A successful inequality must
be matrix/`R^omega` specific (or follow from LLP/stability), separating CE
microstates from the unavoidable non-CE exact trace.  See
`ATLAS_BOUNDARY_RANK_THREE_EXACT_AUDIT.md`.

### 2026-08-12: representation universality stops at the character boundary

Chifan--Drimbe--Ioana embedding universality does not turn Manzoor's non-CE
equivalence-relation factor into a group factor.  It embeds the factor in a
non-CE factor generated by a representation of any chosen acylindrically
hyperbolic group, but the resulting factorial character need not be regular.
The source explicitly records embedding universality of group factors as
open.  The exact remaining bridge is now banked: an acylindrically hyperbolic
group whose nonregular extremal characters are all CE would be nonhyperlinear.
Charmenability with trivial amenable radical would suffice, but no known
group lies in that overlap.  See `FALSE_RECENT_LITERATURE_AUDIT.md`, Section
7.  Do not cite factor universality as a discrete-group construction without
proving regularity of the generated character.

### 2026-08-12: consolidate the Clifford endpoint; test finite Hall support

The full fermionic crossed product and the perfect even-core CAR endpoint
are exactly the same CE problem.  If

```text
N_even=A_CAR crossed_product G
```

and `C_o` is one odd Majorana, then

```text
M_full = N_even crossed_product_(Ad C_o) C_2.
```

Parity supplies the grading and conditional expectation.  Hence
`M_full` is CE iff `N_even` is CE: one direction is inheritance by
subalgebras, and the other is finite-crossed-product embedding into
`M_2(N_even)`.  The full model displays the exact relative wall, while the
even model supplies the perfect nonsofic group and canonical CAR character;
do not count them as independent attacks.  See
`PERFECT_CORE_KUN_THOM_WREATH.md` and
`FALSE_FERMIONIC_KUN_THOM_ENDPOINT.md`.

For the Leavitt atlas, finite coefficient extraction now has a sharper
support-only test.  If a unitary block matrix `W in M_m(D)` is forced to map
source sectors `S` only into target sectors `T`, then

```text
(1/m) sum_(j in S, i notin T) ||W_ij||_2^2
    >= (|S|-|T|)_+/m.
```

Thus a Hall-deficient root-character support graph gives a uniform defect
floor without reconstructing a full Leavitt family.  The bare four-by-four
comb support is Hall-balanced, so the deficit must appear only after the
Pauli/root-sector compression.  If no such deficit occurs, the next target
is the one-cut estimate `(RPC47)`: zero lower leakage and positive upper
leakage across the rank-three-versus-one comb cut.  See
`ATLAS_RELATIVE_PERFECTNESS_AND_COEFFICIENT_ENDPOINT.md` and
`HIGHEST_YIELD_NONHYPERLINEAR_ATTACK.md`.

There is also a strictly smaller multiplicative endpoint.  Four contraction
blocks satisfying `T_0S_0~=1`, `T_1S_1~=1`, and `T_0S_1~=0` have maximum
normalized-HS defect at least `2-sqrt(3)>1/4`, independently of dimension.
This stronger bound and its rational `1/4` corollary are now formalized in
`Sofic/LeavittTraceFloor.lean`.  Hence no additive Cuntz--Leavitt relation has
to be recovered from group microstates.  The extraction target is now just
these three products in one coherent Pauli coefficient corner; their
coefficient values are already the fixed Steinberg commutators landing at
`1,1,0`.  See `(RPC108)--(RPC119)`.

The existing exact radius-five collision scan also closes the naive linear
Hecke version: after (H)-alignment there are zero words with exactly one
transverse second-chart syllable, so this window yields no direct
`W A = B W` synchronization edge.  Any Hall/one-cut extraction must use
quadratic-or-higher block equations or a new relation packet.

The central root tree by itself is also closed as a Hall source.  At binary
depth `r`, its `2^(2^r)` Fourier characters have equal trace.  One compressor
maps a source character to all `2^(2^r)` extensions on the unused subtree;
the target weights shrink by exactly the reciprocal factor.  Thus every
source set has neighbourhood of exactly the same total trace weight.  This
remains true on the negative source-root sector because compression fixes
only the chosen subtree sign, leaving the other subtree free.  A useful
finite-support obstruction must therefore include the raw second compressor
and adjacent noncentral roots, rather than merely deeper central roots.

This no-go is now exact for atomic Hellinger arguments on every finite
additive coefficient window, not only on diagonal cylinders.  Span the
finite orbit window under the injective corner maps, extend each partial
injection to an automorphism by basis completion, and average over the dual
space.  The result has exact local compressor covariance and the regular
Fourier law on the whole chosen window.  Hence every argument using only
finite additive root moments and injective linear corner transport admits an
exact finite countermodel.  The atlas attack must use coefficient
multiplication, cross-root commutators, or noncentral/Pauli data.  See
`(RPC85)--(RPC107)` in
`ATLAS_RELATIVE_PERFECTNESS_AND_COEFFICIENT_ENDPOINT.md`.

More generally, no Hall deficit can be built solely from ambient subgroup
spectral projections: the exact Leavitt representation inside the finite
tracial algebra `L(Q)` obeys the same universal support relations, and trace
forces every such neighbourhood to have at least the source weight.  Hall is
still live only after the non-intrinsic canonical regular-chart
disintegration, in the finite block-coefficient/multiplicity algebra.  The
raw compressor and adjacent roots are inputs to that coefficient
calculation, not themselves ambient deficient projections.

### 2026-08-13: the overlap spherical gauge is only one `2 x 2` block

An exact `GL_4(2)` character calculation identifies the atlas overlap
`H=diag(GL_3(2),1)` as the stabilizer of a nonincident point--hyperplane flag.
Its 120-point permutation module is

```text
Ind_H^A8(1) = 1 + 2(14) + 35 + 56.
```

The point and hyperplane modules are both `1+14`; their normalized cross Gram
operator has singular value `1/4` on the zero-sum 14-space.  Consequently the
spherical commutant has dimension seven and the entire non-scalar ambiguity
is a single `U(2)` rotation on the two 14 copies.  The 35 and 56 sectors have
scalar gauge.  The raw-compressor recovery audit should now test those two
multiplicity-one sectors first and reduce to the fixed `2 x 2` doublet only
if necessary.  See `TRUE_ATLAS_NONINCIDENT_FLAG_TYPE_REDUCTION.md` and the
MSI replay `atlas_nonincident_flag_character.g`.

### 2026-08-13: raw compressors compiled back into `A8*A8`

The scalarized raw swap and comb compressor now have exact reduced source
words of lengths `25` and `175` in the two finite atlas factors.  A recursive
Steinberg compiler translates each prefix transvection through the thirty
atlas roots and exact all-depth Leavitt evaluation replays both complete
words.  This removes the last source-coordinate ambiguity before the
spherical 35/56/14-doublet audit: every packet element can now be evaluated
from the two chart representations and the relative unitary, without
inserting characteristic-two matrix entries by hand.  See
`TRUE_RAW_COMPRESSOR_TWO_CHART_SOURCE_WORDS.md` and
`atlas-raw-compressor-source-words.json`.

### 2026-08-13: the direct classical spherical packet collapses

Exact amalgam normal forms close the proposed 35/56 scalar test negatively.
After the certified inner alignment, the 25-syllable raw swap and the
175-syllable comb both reduce to the identity in `A8 *_H A8`.  The hard
class-11 prefix and next letter each reduce to a single element of the
amalgamated subgroup `H`.  Hence the complete packet has no nontrivial
closed holonomy on the aligned `1+2(14)+35+56` flag module; neither the
multiplicity-one scalar channels nor the 14-doublet can see the Leavitt
two-child class at order zero.

This does not trivialize the source words in the Leavitt atlas group.  It
proves that their nontriviality is transverse coefficient data killed by the
classical amalgam quotient.  Together with the all-fields first-order
certificate, it rules out fixed spherical characters and formal
deformations of the aligned fold.  Continue only on the nonclassical branch:
condition on the certified Reynolds misalignment, extract the nonlinear
`H`--`H` bimodule block products of the compiled words, and then seek a
gauge-invariant two-child or one-cut leakage contradiction.  See
`FALSE_CLASSICAL_SPHERICAL_RAW_PACKET_COLLAPSE.md` and the MSI replay
`atlas_raw_compressor_amalgam_audit.py`.

### 2026-08-13: the raw word gives a direct fixed Reynolds gap

The classical collapse has a sharp quantitative converse.  Every one of the
twelve second-chart syllables in the 25-letter raw source word lies in `H`,
and replacing those twelve copies by the first chart makes the word exactly
trivial.  Bi-unitary invariance and telescoping give

```text
||r_src(U)-1||_2 <= 12 Delta_H.
```

The Leavitt image proves `r_src!=1`, so trace-preserving hyperlinear
separation makes the left side tend to `sqrt(2)`.  Consequently

```text
Delta_H >= sqrt(2)/12-o(1),
1-||E_H(U)||_2^2 >= 1/13440-o(1).
```

The improved Reynolds constant uses the exact multiplicities `8,4` of the
only two distinct second-chart `H`-letters: their squared displacement sum
is at least `1/40-o(1)`.  This removes the enormous `A8` diameter loss from
the earlier Weyl-bridge bound and excludes an explicit Reynolds tube around the classical fold.
Continue the nonlinear coefficient audit only in this fixed annular regime.
See `TRUE_RAW_WORD_REYNOLDS_GAP.md` and the one-core MSI replay
`atlas_raw_reynolds_gap_audit.py`.

The two named letters are involutions whose product has order three, and
their exact subgroup closure has order six: `K=GL_2(2)~=S3`.  The six-term
Reynolds identity upgrades the localized deficit to

```text
1-||E_K(U)||_2^2 >= 1/480-o(1).
```

Use the three irreducible `S3` types `1,sign,2` as the next finite
multiplicity quiver.  The hard-pair/comb block products must either retain
the two child branches there or furnish an exact certificate that the
restriction is too coarse before the 168-element `H` quiver is expanded.

Exact closure further identifies the raw cell.  Its four distinct
first-chart letters generate another `S3` which centralizes `K`, intersects
it trivially, and gives an order-36 direct product `S3 x S3`.  Hence the raw
word is exactly a transport holonomy between two finite `S3` alphabets.
The class-11 hard prefix and next letter do not normalize `K`: separately
they extend it to order-24 `S4` subgroups, and together they generate the
full order-168 `GL3(2)`.  The smallest live branching diagram is therefore

```text
S4 <- S3 -> S4.
```

The next-letter `S4` is an honest chart subgroup; the prefix `S4` is only
the classical value of a cross-chart word and must be recovered
quantitatively.  See `TRUE_RAW_WORD_S3_TIMES_S3_LOCALIZATION.md`.

The exact complex branching matrix `S4 -> S3` is multiplicity-free, with
rows `1`, `sign`, `standard_2`, `1+standard_2`, and
`sign+standard_2`.  Its regular dimension vector restricts as
`(4,4,8)`, exactly four regular `S3` vectors.  The resulting type graph is
Hall-balanced on both hard extensions.  Do not pursue type counts alone;
retain the nonlinear multiplicity arrows through the shared standard
`S3` channel.  See `FALSE_S3_S4_TYPE_ONLY_HALL_DEFICIT.md` and the MSI GAP
replay `atlas_s4_s3_branching.g`.

### 2026-08-13: the raw word is an intrinsic trace-half coefficient cut

Over the actual characteristic-two Leavitt ring, the raw word is a
nontrivial involution and centralizes the compressed core.  These statements
are kernel-checked as `rawInvolutionWord_sq`,
`rawInvolutionWord_ne_one`, and
`rawInvolutionWord_commutes_compressed_core`.  In a hypothetical
trace-preserving hyperlinear embedding,

```text
e=(1-r)/2
```

is therefore an intrinsic projection of trace exactly `1/2` in the
compressed-core commutant.  If `C=Core'` and `D=alpha(Core)'`, then
`C subset D=uCu*`, `e in D`, and `u*eu in C`.  This supplies a canonical
positive-density carrier without interpreting any characteristic-two XOR
sum over the complex matrices.  It does not yet recover the compatible
finite-coordinate nesting `C_n subset D_n`, and ambient traciality alone
cannot do so.  Continue either with that coordinate-commutant theorem or by
extracting the hard/comb two-child arrows on the trace-half carrier.  See
`TRUE_RAW_INVOLUTION_SPECTRAL_CUT.md`.

### 2026-08-13: hard-pair Leavitt star is not group inverse

The short formula for `p_001` cannot be converted into a complex spectral
polynomial by reading Leavitt `star` as operator adjoint.  In the first
class-11 pair, `q` has order four but `q^star != q^-1` (and likewise for
`l`).  The correct four-term Leavitt-star formula is the nonzero `p_001`,
whereas inverse substitution makes it exactly zero:

```text
1 + q^-2 + q^2 + q^-2 q^2 = 0.
```

Therefore retain the root-character/Steinberg coefficient disintegration;
do not apply operator star to the printed characteristic-two certificate
before that corner has been recovered.  See
`FALSE_HARD_STAR_IS_GROUP_INVERSE.md`.

### 2026-08-13: the raw cut lies in the Pauli coefficient factor

Let `H_0` be the compressed order-eight root Heisenberg group generated by
`x_12(p_0),x_23(p_0)`, with central commutator `Z=x_13(p_0)`.  Exact
Leavitt arithmetic gives

```text
<H_0,r> = H_0 times C2,
```

of order `16`.  On the `Z=-1` Pauli sector, `r` therefore acts only on the
multiplicity factor.  Regular trace makes the joint `(Z=-1,r=-1)` corner
have trace `1/4`, so after normalizing the Pauli sector the raw negative cut
has coefficient trace exactly `1/2`.  This crosses the carrier-placement
gate: the cut is honest, coefficient-valued, and positive-density.  Next
compute comb/hard leakage relative to this cut.  See
`TRUE_RAW_PAULI_COEFFICIENT_CUT.md`.

### 2026-08-13: synchronize Leavitt star by one finite extension

For group units, inverse followed by Leavitt/matrix transpose is an
involutive automorphism `psi`.  The semidirect candidate
`Q^sharp=Q semidirect_psi C2` supplies a spatial involution `J` with
`pi(theta(g))=J pi(g)^* J`.  The raw involution is fixed by transpose, so
`J` preserves its two equal Pauli coefficient halves.  On the compressed
`GL3(2)`, `psi(g)=(g^-1)^T` is outer; the synchronized finite chart has
order `336`, or `672` after adjoining the commuting raw sign.  This closes
the adjoint half of root-character extraction without making the false
`Leavitt star = group inverse` substitution.  Addition and multiplication
must still be extracted through root products and Steinberg commutators.
See `TRUE_RAW_STAR_SYNCHRONIZED_SECTOR.md`.

### 2026-08-13: the finite raw branch cell is `D8 times D8`

The compressed root `D8` commutes with a second `D8` generated by the raw
word and `x_13(p_1)`, giving an exact order-64 Pauli cell.  Lifting the two
hard cylinder projections into one root subgroup gives
`<r,z_11,z_001> = D8 times C2`.  In the joint central negative sector the
two candidate arrows are orthogonal trace-`1/8` arrows, but they fill a
trace-`1/4` carrier, so ambient Pauli calculus is exactly trace-balanced.
The remaining operation is no longer star, canonicity, or positive density:
it is converting the ring product identity `p_child p_parent=p_child` into
spectral support containment through cross-root Steinberg coefficients.
The first hard prefix meets the order-64 cell only in `1`, confirming that
ordinary finite-subgroup branching cannot supply this multiplication.  See
`TRUE_RAW_BRANCH_PAULI_CELL.md`.

The bare multiplicative commutator table is now also closed as a standalone
endpoint.  It has an exact left-regular model in the order-32 extraspecial
two-qubit group: `[X_i,Z_j]=c^(delta_ij)`, with zero trace on every
nonidentity element.  Hence the relations `t_i s_j=delta_ij` only produce a
Pauli pairing until a raw-compressor relation identifies the three distinct
central-character fibers.  The precise remaining statement is the
fiber-identification gate in `(RPC120)--(RPC124)`; finite Clifford
normalizers do not cross it.

The fiber gate now has a basis-free algebraic formulation.  For
`b_ell(a,b)=ell(ab)`, quotient the first variable by its left radical and the
second by its right radical.  Right multiplication by `t_i` and left
multiplication by `s_j` descend and obey
`b_ell(a t_i,s_jb)=delta_ij b_ell(a,b)`.  No finite nonzero nondegenerate
pairing can carry these four arrows: the diagonal cases make the `t_0` and
`s_1` arrows bijective, and the cross case then annihilates the whole
pairing.  The remaining atlas theorem is precisely a robust extraction of
these two finite radical quotients and their arrows from normalized-HS
microstates.  Analytically the extracted pairing must be Fourier-flat
(unitary after normalization), not just nondegenerate.  Otherwise its
condition number can diverge and the reduction to the dimension-free
contraction gap is invalid.  The exact target is `(RPC128)`: control
`R_0^*UL_0-U`, `R_1^*UL_1-U`, and `R_0^*UL_1` for a unitary pairing `U`.
Any singular-value-truncation substitute must additionally retain positive
normalized trace and be asymptotically invariant under all four arrows.  See
`(RPC125)--(RPC129)`.

There is also a mandatory trivial-mode reduction.  The perfect `F_2` pairing
produces the unitary normalized Fourier matrix
`|V|^(-1/2)(-1)^(b(v,w))`, not a unitary `0/1` pairing matrix.  Under the
cross identity `b(Rv,Lw)=0`, this Fourier matrix becomes the rank-one
constant kernel.  It vanishes only after deleting the constant source mode
and target delta-at-zero mode.  The analytic gate must therefore prove
near-bijectivity of the approximate arrows and asymptotic invariance of the
reduced Fourier sectors; algebraic nondegeneracy alone does not do so.
## 2026-08-13: perfect-completeness mask audit

The Taller--Vidick LCS compiler was checked at the exact equations.  Its
honest loss occurs precisely when the random mask satisfies
`mu(phi)=-1`, while soundness uses the multiplier
`(1-2 epsilon)^|beta|`.  A mask distribution is perfectly complete only if
it is identically `1` on the support of the honest assignment PVM.  Noise
outside that support gives at best the `1/|S|` uniform-decoding constant,
which is exactly the source projection game's random-guessing floor.
Exposing `mu(phi)` as a correction variable makes every Fourier character
an exact solution.  Therefore mask retuning, support-tailored noise, and a
linear correction variable cannot reach perfect completeness with a strict
soundness gap.  Full proof: `FALSE_PERFECT_COMPLETENESS_MASK_NO_GO.md`.

## 2026-08-14: perfect BCS conversion stops before solution groups

Fu--Mastel--Zhang's perfect-completeness conversion is between two formats
of **general** binary constraint-system games.  It preserves arbitrary
Boolean predicates; it does not turn them into affine/parity LCS predicates.
The obvious group-relator translation cannot do so.  Relations among
commuting involutions cut the joint character cube by affine equations, and
adding then eliminating commuting ancillas still produces an affine set.
For instance the three-point satisfying set of two-bit OR is not affine.

Finite nonabelian truth-table gadgets do not repair this.  If `D` is the
local Boolean subgroup of a finite gadget `F`, `z` is central, and `chi` is
any character of `D` compatible with `z=-1`, then
`Ind_(<D,z>)^F(chi)` is a nonzero finite-dimensional negative-sector
representation whose restriction still contains `chi`.  Thus every
compatible Boolean atom survives some finite-dimensional representation of
the gadget.

Therefore this recent compiler does not close Taller--Vidick's explicit
`epsilon=0` LCS gate.  A successful groupification still needs a nonabelian
multiplication gadget together with a dimension-independent decoding theorem
for approximate representations.  See
`FALSE_PERFECT_BCS_IS_NOT_PERFECT_LCS_COMPILER.md`.
### 2026-08-13: two exact no-go theorems for the remaining routes

- `FALSE_COMPACT_BOGOLIUBOV_APPROXIMATION_FOR_KUN_THOM.md` proves that
  infranormality makes the closure of `Gamma` normal in every compact image
  of `G`.  Thus the distinguished quasi-regular coset mode cannot be
  approximated through honest finite-dimensional representations, closing
  the naive fermionic second-quantization construction.
- `FALSE_PROPERLY_INFINITE_CENTRAL_GROUP_CORNER.md` records the canonical
  regular-trace obstruction: every nonzero finite central-character corner
  of a discrete group has positive finite trace.  The Leavitt atlas cannot
  force proper infiniteness in such a group corner; a matrix-specific
  non-CE separation remains indispensable.

### 2026-08-13: an involutive twist is a normalizer-lifting problem

`FALSE_INVOLUTIVE_TWIST_IS_NOT_SHULMAN_DOUBLE.md` audits the apparent
extension of Shulman's swap proof to `A *_(id,alpha) A`.  After doubling,
the swap implements `alpha` on the edge; it does not commute with the edge.
The Halmos off-diagonal terms therefore contain the full difference
`c-alpha(c)`, which quasicentrality cannot remove.  The virtually-cyclic
central-radical shear still requires a genuine equivariant edge lift.

### 2026-08-13: the opposite Kun--Thom endpoint is HS stability

`KUN_THOM_HS_STABILITY_TO_NONHYPERLINEAR.md` proves that every
finite-dimensional unitary representation kills the standard Kun--Thom
commutator word, using normality of the Iwahori closure in compact images.
Consequently flexible/local Hilbert--Schmidt stability of either the
free-lamp or commuting-lamp witness would make it explicitly
nonhyperlinear.  The recent ordinary-lamplighter stability theorem does not
cover this nonsofic Kazhdan coset action, so this is a clean alternative
endpoint rather than a completed proof.

### 2026-08-13: measured-full-group density cannot groupify Manzoor

There is an exact group-factor certificate: if a countable subgroup
`Lambda` of the measured full group acts essentially freely and its
canonical groupoid unitaries generate `L(R)`, then

```text
L(Lambda) = L(R).
```

Thus a non-CE relation would give a nonhyperlinear group.  Uniform density
cannot provide such a subgroup.  If `T` has a positive-measure fixed set,
every nonidentity element of an essentially free subgroup stays at uniform
distance at least `mu(Fix(T))` from `T`.  Aperiodic full groups have
nonidentity elements of arbitrarily small support, so no essentially free
subgroup is uniformly dense.  Topological finite-generation and the 2026
Cantor-minimal character classification therefore do not convert Manzoor's
relation into a discrete group.

There is a stronger exact no-go.  If `Lambda<=[R]` is essentially free, the
Cartan expectation satisfies `E_A(u_g)=0` for every `g!=1`, hence
`E_A(W*(u_Lambda))=C1`.  Therefore `W*(u_Lambda)` cannot equal `L(R)` on a
nontrivial probability space, since the latter contains the diffuse Cartan
`A` and `E_A|A=id`.  The proposed free W*-generating subgroup is therefore
impossible, not merely difficult to construct.  Any Manzoor groupification
must embed the non-CE algebra into a group factor by additional operators or
as a corner, rather than identify it with the algebra of canonical full-group
implementers.  See `FALSE_FULL_GROUP_DENSITY_GROUPIFICATION.md`,
`(FDG4a)--(FDG4d)`.

### 2026-08-13: an unnormalized Schatten-one central-radical corner is enough

`TRUE_SCHATTEN_ONE_RADICAL_CORNER.md` proves a new norm-to-trace converter.
If a countable group `E` has a nontrivial central involution
`z in Rad_sof(E)`, then any unnormalized Schatten-one asymptotic
representation which retains `z` can be rounded at `z`, compressed to its
nonzero negative spectral corner, and renormalized.  On a corner of rank
`r>=1`,

```text
||A||_(2,r)^2 <= 2||A||_1/r <= 2||A||_1,
```

so the compressed maps are normalized-HS asymptotic representations, while
the rounded `z` becomes exactly `-1` before the negligible polar correction.
Thus the radical element survives and the ultraproduct image is hyperlinear
and nonsofic.  This requires neither positive original corner density nor
hyperlinearity of `E/<z>`.  It supplies the new sufficient endpoint that the
explicit cyclic shear be unnormalized-Schatten-one approximated.  It does
not follow from Bachner--Dogon--Lubotzky's non-`G1` result, and normalized HS
defect cannot be promoted to unnormalized `L1` without a missing
dimension-versus-error rate.

### 2026-08-13: the Kun--Thom radical and Clifford sign are the same phase

`TRUE_KUN_THOM_CLIFFORD_PHASE.md` gives a direct algebraic phase lock.  For
`H=<G,k | k^2=1,[k,Gamma]=1>`, choose
`h=t^(-1)gamma t notin Gamma`.  Kun--Thom centralizer normalization puts
`r=[k,h]` in `Rad_sof(H)`, hence also `x=[k,r]`.  In the Clifford crossed
product on `X=G/Gamma`, map `G` to its canonical crossed-product unitaries
and `k` to the Majorana at the base coset.  Then

```text
r |-> c_Gamma c_(hGamma),          x |-> -1.
```

Thus the radical-collision program no longer needs a separate algebraic
phase coupler: the second commutator is already the scalar Clifford sign.
The identity is Lean-verified by
`CliffordLamp.commutator_lamp_lamp_mul_lamp`.
The exact remaining gate is Connes embeddability of
`Cl(G/Gamma) crossed_product G` for the explicit Kun--Thom pair.  The base
is hyperfinite, but the action is nonsofic and not profinite; arbitrary
crossed-product permanence would silently assume the missing theorem.
An even weaker sufficient matrix gate is now explicit: find HS-asymptotic
representations `rho_n` of `G` and self-adjoint involutions `C_n` which
asymptotically centralize `rho_n(Gamma)` while `C_n` asymptotically
anticommutes with `rho_n(h)C_n rho_n(h)^*`.  This alone sends the radical
word `x` to `-1`.

### 2026-08-13: the parity shear can be innerized, but the MF gate remains

`TRUE_SHEAR_INNERIZATION_REDUCTION.md` gives an exact algebraic reduction.
For an infinite-order `s in Rad_sof(G)`, the universal module

```text
A=F_2[G]/I(1+s),       E=A semidirect G
```

contains an involution `tau` with

```text
tau^(-1) s tau=z s,
```

where `z=(1+s)[1]` is a nontrivial central sofic-radical involution.  Hence
the edge automorphism `s|->zs`, `z|->z` is inner in `E`, and the associated
twisted double embeds, by Bass--Serre normal form, in the ordinary symmetric
double `E *_C E`.  This makes Shulman's symmetric-amalgam theorem applicable
*if* `E` is weak MF.  The qualification is essential: `z=[tau,s]` already
lies in `Rad_sof(E)`, so weak MF of `E` alone would solve hyperlinear versus
sofic by central-corner compression.  Innerization eliminates the twist as
an additional obstruction; it does not establish the missing matrix
approximation.

### 2026-08-13: character rigidity does not splice into universality

`FALSE_CHARACTER_RIGIDITY_EMBEDDING_UNIVERSALITY_SPLICE.md` audits the
tempting use of Chifan--Drimbe--Ioana.  Their factor `Q` is generated by a
representation of any chosen acylindrically hyperbolic group and can contain
a non-CE algebra, but the resulting factor character is not the regular
character of the image group.  Property `(T)`, hyperbolicity, and absence of
one-dimensional characters do not repair this.  The missing statement is
factor-character rigidity after kernels, which is available in higher-rank
arithmetic settings incompatible with the embedding-universal source.  The
splice therefore restates the open group-factor universality problem rather
than solving it.

### 2026-08-13: a relative Burton gate would make Kun--Thom nonhyperlinear

`TRUE_RELATIVE_BURTON_KUN_THOM_REDUCTION.md` gives a direct reduction for
the universal-hyperlinearity problem.  If the Kun--Thom commuting-lamp group

```text
W=(direct_sum_(G/Gamma) C_2) semidirect G
```

were hyperlinear, restrict a canonical-trace matrix model to its amenable
lamp subgroup.  The quantitative theorem of
Burton--Chaudkhari--Juschenko--Muliarchyk replaces that restriction, on
increasing finite sets and in normalized HS norm, by permutation matrices.
The quotient matrices still satisfy

```text
U_g sigma(a) U_g^* ~= sigma(gag^(-1))
```

and remain an HS-asymptotic representation of `G`.  Hence it is enough to
prove one equivariant normalizer-transfer theorem: these coherent unitary
normalizers can be replaced, after `o(d)` padding, by coherent permutation
normalizers.  The resulting semidirect-product permutations would make `W`
sofic, contradicting Kun--Thom; therefore `W` would be explicitly
nonhyperlinear.

The new endpoint is narrower than general tracial commutant recovery.  The
fixed finite lamp restrictions have asymptotically regular character, so
ordinary atom-weight and fixed-rank Gassmann defects disappear.  What
remains is coherence across increasing non-invariant lamp patches.  The
amenable conversion theorem alone does not preserve the ambient normalizer
cocycle, and independently extending each partial coset permutation assumes
the missing action-soficity.  The lamp patches have an additional exact
quantization:

```text
[B_Y:B_Y intersect B_(gY)]=2^|Y-gY|.
```

Hence overlap tending to one forces eventual exact invariance; there is no
Folner-style uniform-lamp interpolation.  A proof must recover coherence
from the ambient unitary cocycle rather than from enlarging finite coordinate
sets.

`TRUE_FINITE_REGULAR_NORMALIZER_ROUNDING.md` now proves the complete
finite-dimensional step after such a common lamp model has been recovered.
For equal-rank spectral blocks, blockwise polar decomposition rounds an
approximate transport with no dimension-dependent loss.  Fourier Parseval
identifies the required block defect with the average lamp covariance defect,
and multiplication descends to block-label Hamming distance.  For
`(C_2)^m`, two distinct linear block actions have Hamming distance at least
`1/2`, so sufficiently accurate relators become exact finite linear
relators.  Thus phases and growing regular multiplicities are not a remaining
obstruction; the sole gate is recovery of one common finite lamp algebra
approximately normalized by the quotient generators.

`TRUE_FINITE_LAMP_GROUPOID_ROUNDING.md` extends this to a finite diagram of
different regular lamp partitions.  Every unitary arrow rounds with the same
dimension-free constant, and coherent products descend to Hamming-coherent
linear label maps; the `1/2` gap makes a fixed multiplication table exact.
Thus moving between finitely many translated lamp windows creates no new
analytic or block-cocycle loss.  What remains is completion of the finite
prefix objects to one finite quotient-action object set.  Existing flexible
stability of finite groupoids assumes that object set and therefore does not
supply this completion.

There is a necessary information warning.  The rounded linear label maps are
canonical maps coming from the original coset action; by themselves they know
nothing about the hypothetical hyperlinear model.  Completing them without
using the internal regular-block unitaries would assume a finite approximation
of the already nonsofic action.  The next live invariant is therefore the
multiplicity-block holonomy around finite word-prefix diagrams: it must either
force object completion or carry a uniform HS defect.

### 2026-08-13: Clifford hyperlinearity forces instability of the ambient group alone

The perfect even Clifford cover sharpens the existing stability endpoint.
If the cover were hyperlinear, its regular character would have a trace-`1/2`
negative central corner. Character rigidity identifies that corner with the
canonical CAR trace. CAR microstates then give a normalized-HS asymptotic
representation of the classical ambient group `G`, together with a root
Majorana commuting asymptotically with `Gamma` but staying at distance
`sqrt(2)` from its strict predecessor conjugate. The relative-wall theorem
therefore implies that `G` is not flexibly normalized-HS stable.
Equivalently, flexible normalized-HS stability of `G` alone would make the
perfect Clifford cover an explicit nonhyperlinear group.

There is a crucial normalization firewall: 2-Kazhdan cohomology yields
stability for the unnormalized Frobenius norm, whereas arbitrary CE
microstates provide only normalized-HS defects. One additionally needs
`sqrt(d_n) epsilon_n -> 0`, and neither CE nor subsequence selection
provides that rate. Thus the existing coefficientwise `H^2` gate cannot
be advertised as closing the Clifford argument. Full proof and scope:
`TRUE_CLIFFORD_HYPERLINEARITY_FORCES_AMBIENT_HS_INSTABILITY.md`.

### 2026-08-14: the central-regular Iwahori obstruction is a sparse outlier

`TRUE_IWAHORI_CENTRAL_REGULAR_OUTLIER_LOCALIZATION.md` sharpens the
Dogon--Vigdorovich lane.  On the remaining central-regular sequence, the
mixed edge representation on Hilbert--Schmidt space converges in normalized
character to the regular representation of `Z*C_2`.  Nonamenability and
Kesten's gap force every fixed low-energy spectral projection to have rank
`o(d_n^2)`, while the near-intertwining identity vector lies asymptotically
inside it.

The bulk is therefore closed.  The remaining statement is full-rank
outlier repair: exploit the fact that the sparse low-energy space comes from
restrictions of two exact `SL_2(Z)` representations, and turn its vector
near `1_(d_n)` into an exact invertible edge intertwiner with only `o(d_n)`
padding.  An arbitrary sparse operator subspace need not give sparse
physical rank, so this is still a genuine theorem rather than a dimension
count.

The spectral outlier is invariant under the left and right edge commutants.
It decomposes into low-energy `Hom(theta_j,pi_i)` spaces tensored with full
multiplicity rectangles, and almost all identity mass lies in those blocks.
Thus the live case is even narrower: high-dimensional edge irreducible pairs
which extend through opposite modular vertices, have collapsing mixed gap,
and carry a near-unitary low-energy intertwiner.  Bounded types were already
removed by the fixed-type and dimension-tight matching theorems.

### 2026-08-14: equivariant whole maps permit exact rectangular escape

`FALSE_EQUIVARIANT_WHOLE_MAPS_ALLOW_RECTANGULAR_ESCAPE.md` corrects the
scope of the new orbit-summing theorem.  If `b` is a finite perfect pairing,
the direct-sum target pairing and the four coordinate embeddings satisfy the
entire diagonal-one/cross-zero Leavitt table exactly.  These maps are already
deterministic and translation-equivariant.  Source Weyl multiplicity can be
traded for a larger target Weyl factor in the same total matrix dimension,
so unitary compressor covariance does not identify source and target label
sizes.

The remaining theorem is same-orbit paired-translation closure on positive
trace.  Once the child images are known to stay in one source-sized finite
orbit, equivariant orbit-summing supplies a common law of self-maps and the
robust `1/36` floor applies.  A literal covariance audit alone cannot prove
the closure clause.

### 2026-08-14: equivariant transition PVMs give whole response maps

`TRUE_EQUIVARIANT_TRANSITIONS_COARSEN_TO_WHOLE_MAPS.md` closes the abstract
gap from per-source extension outcomes to counterfactual whole maps under
paired-translation equivariance.  Pull all response PVMs on a free
translation orbit to one base block.  Exact equivariance makes them equal,
and orbit-summing base outcomes yields a PVM indexed by whole affine response
maps.  For approximate equivariance, averaging and de la Salle rounding give
a universal total squared error bound `40 epsilon`, with no orbit-size,
alphabet, or matrix-dimension loss.

The literal input for this step is to check that each raw/comb one-sided
Leavitt transport conjugates the named middle-root commutators to the
corresponding target translations.  The intrinsic transition PVM is then
equivariant by a direct conjugation calculation.  Applying the `1/36` floor
still additionally requires the source and target translations to act on
the same finite paired orbit; rectangular enlargement is the remaining
matrix-specific gate.

### 2026-08-14: nested commutators recover both radical translations

`TRUE_NESTED_COMMUTATORS_RECOVER_PAIRED_TRANSLATIONS.md` replaces an
arbitrary coefficient-gauge decoder by named group words.  On the long-root
sector `ell`, `[x_23(1),x_34(b)]` shifts the `x_12` character by
`a |-> ell(ab)`, while `[x_12(a),x_23(1)]` shifts the `x_34` character by
`b |-> ell(ab)`.  The kernels are exactly the two radicals.  The physical
unitaries force flat spectral multiplicity on their translation orbits, and
Fourier Parseval identifies approximate nested-commutator error with twice
the total wrong-shift mass, uniformly in packet size.

The paired quotient is therefore already visible inside the mixed root
representation.  The remaining theorem is only a growing-window closure
estimate: the four right/left Leavitt transports must have vanishing boundary
leakage on these same recovered finite translation groups.  Once that is
proved, the `1/36` or `2-sqrt(3)` contradiction is immediate.

### 2026-08-14: exact joint compressor covariance permits maximal fiber variance

`FALSE_EXACT_JOINT_COMPRESSOR_HAS_MAXIMAL_FIBER_VARIANCE.md` gives the exact
finite countermodel to an additive-only completion of the new common-
compressor route.  For an injection `F->G`, diagonalize `G` on `l2(G^)`,
restrict to `F`, and take the compressor to be the identity.  The intrinsic
extension-character PVM, joint left/right covariance, and every finite-depth
path identity are exact.  A branch bit balanced on every restriction fiber
still has conditional variance `1/4`, and this can be repeated at every
level of a growing chain.

Thus common-compressor synchronization closes the relative PVM gauge but
does not approach the decoder by itself.  The next positive statement must
be a mixed multiplication-to-variance estimate: the nested middle-root
Leavitt table must bound the two outer fiber variances with constants
independent of packet size and matrix dimension.  Pure covariance energy is
zero in the countermodel and cannot appear as the missing term.

### 2026-08-18: commuting sofic actions do not combine — GKP Question 4.2 closed

Question 4.2 of Gao--Kunnawalkam Elayavalli--Patchell (arXiv:2401.04945,
*Res. Math. Sci.* 12 (2025), 48) has a negative answer: there are two
commuting **free sofic** actions of one sofic group whose combined
`G x G`-action is not sofic.  The construction is the diagonal coset space
`X = (G x G)/(Delta Gamma)` over the Kun--Thom pair
`Gamma = EL_r(R_+) <= G = EL_r(R) : SL_d(Z)` — each coordinate action is free
(a diagonal element with a trivial coordinate is trivial), while the diagonal
copy of `G` cuts out an orbit isomorphic to the nonsofic coset `G`-set
`G/Gamma`.  Graph: `commuting-sofic-actions-need-not-combine` (root, ESTABLISHED)
via `commuting-counterexample-from-kun-thom-pair` and
`nonsofic-orbit-forces-commuting-counterexample`; circulation note at
`research/artifacts/commuting-sofic-actions-note-2026-08-17.md`.  The
group-theoretic core is kernel-checked in
`GroupApproximation/Algebra/DiagonalCosetAction.lean`; the soficity transfers
(GKP Thm 2.14, Props 2.15/2.16) and the Kun--Thom input remain the cited
trust surface.  Priority search 2026-08-17 found no prior resolution; author
confirmation outstanding.
