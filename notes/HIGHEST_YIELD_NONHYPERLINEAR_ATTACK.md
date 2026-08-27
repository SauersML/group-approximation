# Highest-yield remaining attacks: finite-multiplicity reconstruction first

Date: 2026-08-12

## 2026-08-14 central-regular Iwahori mismatch is a sparse outlier

In the only unresolved Dogon--Vigdorovich sector, the mixed edge
representation on `M_(d_n)` has normalized character

```text
tr(rho_n(b)) conjugate(tr(sigma_n(b))),
```

which converges to the regular character of
`B/<z> ~= Z*C_2`.  Kesten's gap therefore implies that every fixed
low-energy spectral window has dimension `o(d_n^2)`.  The identity matrix is
an almost invariant unit vector, so it lies asymptotically inside that
sparse window.  See
`TRUE_IWAHORI_CENTRAL_REGULAR_OUTLIER_LOCALIZATION.md`.

Thus diffuse mixed-gap collapse is impossible.  The Iwahori endpoint is now
a full-rank outlier-repair theorem: an `o(d_n^2)` low-energy operator space
contains a matrix near the full-rank identity, and one must use its origin
from two exact modular vertex representations to turn it into an exact
invertible edge intertwiner after only `o(d_n)` padding.  Spectral sparsity
alone is insufficient because even the scalar line contains invertible
matrices.

The low-energy projection commutes with the left and right edge commutants.
It is therefore a bimodule and decomposes exactly into low-energy
`Hom(theta_j,pi_i)` blocks tensored with the full multiplicity rectangles.
The identity mass must concentrate on such blocks.  Together with the
dimension-tight theorem, this reduces a negative sequence to
high-dimensional pairs of edge irreducibles, each extending through an
opposite modular vertex, whose mixed gap collapses along a near-unitary
intertwiner.  Arbitrary sparse operator subspaces are no longer part of the
gate.

## 2026-08-14 equivariant whole maps still admit rectangular escape

The whole-map theorem does not identify the source and target paired label
spaces.  For every finite perfect pairing `b:V x W->F_2`, the direct-sum
pairing on `V'=V+V`, `W'=W+W` and the four coordinate embeddings satisfy

```text
b'(R_i v,L_j w)=delta_ij b(v,w)
```

exactly.  The maps are deterministic and fully translation-equivariant.
They evade the `1/36` theorem only because their codomains are larger.  At
the matrix level, a source Weyl factor with multiplicity `N` and a target
Weyl factor of size `N^2` both act on dimension `N^2`, so unitary covariance
and trace balance do not close the escape.  See
`FALSE_EQUIVARIANT_WHOLE_MAPS_ALLOW_RECTANGULAR_ESCAPE.md`.

The live theorem is therefore same-orbit closure: on positive total trace,
the two child translation images must remain inside one source-sized paired
orbit up to vanishing boundary leakage.  Equivariant orbit-summing then
supplies the common self-map law, and `1/36` finishes.  Without this closure,
the four-word covariance audit is insufficient.

## 2026-08-14 equivariant transitions produce whole-map PVMs

The named paired translations close the counterfactual-response gap whenever
the actual transition PVM is equivariant under them.  On a free translation
orbit, pull every source-conditioned response PVM to one base block.  Under
exact equivariance these PVMs coincide; orbit-summing each base outcome gives
a PVM indexed by whole equivariant response maps.  With mean total squared
equivariance error `epsilon`, orbit averaging plus cardinality-free POVM
rounding gives an exact whole-map PVM within `40 epsilon`, independently of
orbit size, response alphabet, and matrix dimension.  See
`TRUE_EQUIVARIANT_TRANSITIONS_COARSEN_TO_WHOLE_MAPS.md`.

The additive extension-fiber model is consistent with this theorem: it is a
classical mixture of affine sections even though its branch conditional
variance is maximal.  The Leavitt multiplication table, not source-only
measurability, is what rules out a common mixture of such sections via the
`1/36` floor.

The next literal task is to verify for all four one-sided maps that the
raw/comb transition unitary carries each named middle-root translation to
its transported translation.  This makes the transition PVM equivariant.
It closes the common-map extraction only after the separate same-orbit
closure theorem excludes rectangular target enlargement.

## 2026-08-14 nested commutators recover the paired translations directly

On a long-root character sector `ell`, the named middle-root commutators

```text
D_b=[x_23(1),x_34(b)],       C_a=[x_12(a),x_23(1)]
```

translate the two outer-root character PVMs by the functionals
`a |-> ell(ab)` and `b |-> ell(ab)`.  Their kernels are exactly the right
and left radicals of `b_ell(a,b)=ell(ab)`.  Unitarity makes character
multiplicity constant along every translation orbit.  Averaged approximate
nested-commutator error is exactly twice the total mass outside the required
shift graph, by Fourier Parseval.  See
`TRUE_NESTED_COMMUTATORS_RECOVER_PAIRED_TRANSLATIONS.md`.

This removes arbitrary multiplicity-gauge recovery from the label-level
paired-quotient route.  The remaining analytic gate is closure rather than
reconstruction:
make the four maps `[a] |-> [a t_i]`, `[b] |-> [s_j b]` act with vanishing
boundary leakage on the same finite translation groups recovered above.
Then the exact table `ell(a t_i s_j b)=delta_ij ell(ab)` reaches the existing
`1/36` or `2-sqrt(3)` endpoint directly.

## 2026-08-14 exact joint covariance can retain maximal fiber variance

One common compressor does synchronize the two commuting outer transition
PVMs, but covariance alone cannot decode their many-to-one character fibers.
For every proper finite binary inclusion `alpha:F->G`, represent `G`
diagonally on `l2(G^)`, restrict that representation to `F`, and take the
compressor to be the identity.  Joint `alpha x alpha` covariance and every
finite-depth path identity are then exact.  Nevertheless a branch bit which
is balanced on each restriction fiber has

```text
||B-E_(A_F)(B)||_2^2=1/4,
```

the maximum binary conditional variance.  The construction works on a
whole chain by restricting terminal characters, so deeper windows do not
remove the fresh Bernoulli directions.  See
`FALSE_EXACT_JOINT_COMPRESSOR_HAS_MAXIMAL_FIBER_VARIANCE.md`.

This closes further additive/Fourier refinement as an endpoint.  The live
theorem must quantitatively use the mixed middle-root multiplication words
to rule out the balanced-fiber model on the common long-root carrier.  The
target is now a size-uniform bound from mixed relator energy to the two
outer conditional variances; after it, the majority decoder and `1/36`
floor are already available.

## 2026-08-14 closed: additive index cannot produce a fixed finite phase

The naive transducer `KInd |-> (-1)^KInd` is incompatible with amplification.
Replacing a microstate by `phi tensor I_k` preserves every normalized-HS
defect, trace, separation, and scalar word value. An additive Fredholm or
rank index is multiplied by `k`. Doubling therefore kills its parity while
a marked scalar `-I` remains `-I`; amplification by the order of any finite
character gives the same no-go. See
`FALSE_ADDITIVE_INDEX_TO_FINITE_PHASE_IS_NOT_AMPLIFICATION_STABLE.md`.

An integer index contradiction or an index normalized by a canonically
recovered positive-density spin multiplicity remains possible. What is
closed is the shortcut that turns microscopic leakage into the marked sign
using a determinant, parity, or another finite character without such a
normalization.

## 2026-08-14 locally finite commutants recover at the wrong scale

The increasing finite unitriangular envelopes do solve elementwise
coordinate commutant recovery. After finite-group exactification, choose the
envelope size slowly and Reynolds-average a bounded lift. The exact identity

```text
||X-E_K(X)||_2^2
 =(1/(2|K|))sum_g||rho(g)Xrho(g)*-X||_2^2
```

puts every fixed finite family from the ultraproduct commutant within
`o(1)` of exact coordinate commutants. See
`TRUE_LOCALLY_FINITE_COMMUTANTS_RECOVER_BUT_AT_SHIFTED_SCALES.md`; the
Reynolds identity is already formalized in
`PropertyT/FiniteGroupAverage.lean`.

The compressor nevertheless shifts the exhaustion. If
`alpha(K_m)<=K_(r(m))`, coordinate recovery gives only

```text
C_(r(m)) <= D_m=U C_m U*,
```

not `C_m<=D_m=UC_mU*`. For the unilateral binary shift the left regular
model has `dim(D_m)=2 dim(C_(m+1))` exactly. Thus separate commutant recovery
is closed; the live obstruction is a quantized scale index or a two-branch
relation synchronizing the two scales in one multiplicity corner.

## 2026-08-14 intrinsic transition effects are already positive

The positivity gap in operator-valued coproduct rounding can be avoided.
For a source projection `P`, target character PVM `(Q_j)`, and the actual
compressor matrix `U`, the intrinsic transition effects

```text
A_j=P U*Q_j U P
```

form a POVM in `PMP`. With `E=UPU*`, their total non-idempotence satisfies
the exact identity

```text
sum_j tau_P(A_j-A_j^2)
 =1/(2tau(P)) sum_j ||[E,Q_j]||_2^2.
```

De la Salle's cardinality-free theorem therefore gives a PVM `(R_j)` with

```text
sum_j||A_j-R_j||_2^2
 <(9/2)sum_j||[E,Q_j]||_2^2.
```

See `TRUE_TRANSITION_EFFECTS_REMOVE_THE_POSITIVIZATION_GATE.md`. Unitary
Fourier covariance now also bounds the displayed total commutator energy by
twice the covariance RMS defect, with no target-alphabet loss; see
`TRUE_COVARIANCE_CONTROLS_TOTAL_TRANSITION_VARIANCE.md`. Thus positivity,
rounding, and the entire single-edge measurement problem are closed.

The source commutant gauge cancels from this particular target exactly. If
`[C,P]=0`, replacing `U` by `UC` leaves `UPU*` fixed and conjugates the
effects `P U*Q_j U P` inside the source corner. Hence their total variance is
unchanged. See `TRUE_TRANSITION_VARIANCE_IS_SOURCE_GAUGE_INVARIANT.md`.
The live gate is multi-edge compatibility. Cross-root multiplication must
make the separately rounded transition PVMs commute in the required edge
contexts and label them by one multiplication-compatible character system.
Compiled-word gauge pinning is relevant only at this assembly stage.

This fine-fiber statement itself has a constant-one finite-partition
reduction. For a fine PVM `(Q_x)` and jointly injective coarse label maps,
the fine commutator energy is at most the sum of their coarse energies. The
actual compression is `a |-> s_0 a t_0`, so the required additive
decomposition has four corners

```text
R=direct-sum_(i,j in {0,1}) s_i R t_j.
```

Their four restrictions jointly determine every fine character. See
`TRUE_TWO_COARSE_PARTITIONS_RECOVER_FINE_CHARACTER_PVM.md`. This refinement
is no longer needed for an individual edge, but it gives a constant-one
endpoint once the four corner-label PVMs from different adjacent-root
occurrences have been made compatible. The words `u` and `wu` cannot supply
independent labels because they implement the same compression.

## 2026-08-14 correction: pure four-root words cannot pin the gauge

The coproduct-identification gate cannot use only root covariance and pure
four-root associativity. In the regular representation of `C2`, the
commutant unitary

```text
C=(1+i)/2+(1-i)/2 lambda_s
```

has group-like coproduct defect exactly `1`. Multiplying an exact
intertwiner by `C` preserves every covariance relation and leaves every
root-only four-root word unchanged. See
`FALSE_PURE_FOUR_ROOT_WORDS_CANNOT_PIN_COMPRESSOR_GAUGE.md`.

Therefore the current positive target must explicitly use the comb
compressor's fixed 175-syllable source word, or another mixed relator which
changes under a physical commutant deformation. Right-multiplying the
relative chart conjugator by a chart commutant does **not** provide such a
test: it leaves the represented second chart and every compiled word
literally unchanged. The highest-signal next problem is instead the fixed
one-unitary stability problem on relative chart positions modulo both chart
commutants: bound an intrinsic compiled-word coproduct defect by the atlas
relator energy, uniformly over all representation multiplicities.

## 2026-08-14 proper compressor paths can be synchronized intrinsically

Finite Fourier twirling works for an arbitrary homomorphism of finite
abelian groups, not only an automorphism.  If `alpha:F->G`, the twirl

```text
Q_alpha(X)=(1/|F|) sum_a sigma(alpha(a))* X rho(a)
```

is the Hilbert--Schmidt orthogonal projection onto the exact `alpha`-
intertwiners, with the sharp identity

```text
e_alpha(X)^2=2||X-Q_alpha(X)||_2^2.
```

These repairs are approximately functorial: for contractions on two
composable arrows, if the relevant full and restricted RMS covariance
defects are at most `eta`, the repaired two-edge path is within
`2 sqrt(2) eta` of the repaired composite.  The constant is independent of
group orders, subgroup indices, and extension-fiber sizes.  Its spectral
expansion uses the canonical intermediate character `zeta o beta`, so the
proper Leavitt compressor does not require a choice of representatives in
its many-to-one dual fibers.  See
`TRUE_HOMOMORPHISM_TWIRLING_IS_APPROXIMATELY_FUNCTORIAL.md`.

This removes "dual maps must be permutations" from the live gate.  It does
not remove exact commutant gauges: an exact gauge is already fixed by the
twirl.  The remaining theorem is to assemble these intrinsic path blocks
into the repaired coefficient implementer and identify their four-root path
discrepancy with its genuine coproduct defect.  After that identification,
the coproduct gauge-pinning theorem below applies.

## 2026-08-14 coproduct defects pin commutant gauges

The arbitrary commutant unitary in a finite regular envelope becomes
classical as soon as its genuine group-like coproduct defect is controlled.
If

```text
C=sum_g c_g lambda_g
```

is a scalar unitary gauge, then

```text
min_h ||C-lambda_h||_2
  <= ||Delta(C)-C tensor C||_2,
```

with constant one, uniformly in the finite group. With operator-valued
multiplicity, the exact corepresentation equation makes the coefficients a
PVM, so the gauge is a direct sum of classical right translations. See
`TRUE_COPRODUCT_DEFECT_PINS_COMMUTANT_GAUGE.md`.

Regular-basis Parseval moreover identifies the squared coproduct defect with
the total coefficient idempotence and cross-orthogonality energy. For the
fixed four-label Pauli packet, ultraproduct PVM lifting therefore gives a
dimension-independent qualitative rounding theorem. For growing envelopes,
de la Salle's cardinality-free POVM orthogonalization supplies the final
rounding step once positivity of the coefficient family has been recovered;
that positivization is not automatic for an arbitrary commutant unitary.

This removes a separate gauge-fixing theorem after coefficient
identification. The remaining load-bearing interface is now one
gauge-covariant Parseval statement: identify the averaged four-root word
discrepancy with the coproduct defect of the actual repaired implementer.
Abstract associativity alone still does not provide that identification.

## 2026-08-14 correction: one classified gauge does not scalarize multiplicity

The full-packet right-shift/multiplicity dichotomy does not collapse merely
because the actual compressor gauge has zero coproduct defect. There is an
exact amplified countermodel

```text
A=C[lambda_K(K)] tensor 1,
C=rho_K(g) tensor 1,
F=1 tensor p,               rank(p)=1 in M_4.
```

Here `C` is exactly group-like, `F` commutes with every recovered right
shift and with `C`, but

```text
E_A(F)=(1/4)1,
dist_2(F,A)^2=3/16,
```

and a pure multiplicity unitary has commutator energy `1/2` against `F`.
See `FALSE_ONE_COPRODUCT_GAUGE_DOES_NOT_SCALARIZE_THE_MULTIPLICITY.md`.

Therefore the compiled-word theorem must be carrier-coupled: besides
classifying the gauge, it must make the transported carrier measurable with
respect to the gauge's coefficient PVM, produce enough independent PVMs to
generate the relevant multiplicity algebra, or directly kill the centered
variance of the intrinsic transition effects. Gauge classification by
itself is not the terminal synchronization theorem.

## 2026-08-14 one finite envelope removes pairwise root gauges

Every finite coefficient window and all of its positive-root products fit
inside one finite group `U(V)=1+N(V)`, where `N(V)` is a graded nilpotent
algebra of strictly upper-triangular matrices.  For five coordinates the
closure uses at most four coefficient factors.  The complete
`t_l s_k=delta_(l,k)` branch table can therefore be exactified in one finite
group representation, rather than in separately gauged Heisenberg cells.

See `TRUE_FINITE_UNITRIANGULAR_MULTIPLICATION_ENVELOPE.md`.  This removes
pairwise Stone--von Neumann synchronization from the live gate.  It does not
classicalize the finite packet: its regular representation is still an exact
Pauli countermodel.  The sole remaining datum is the comb compressor matrix
on the multiplicity spaces of this one repaired envelope.  The target is to
derive the two diagonal and one crossed common-coordinate pairing defects
from that matrix.

## 2026-08-14 four-root coherence has no table-size loss

The two parenthesizations of coefficient multiplication are the bounded
four-root Steinberg identity

```text
[[x_12(a),x_23(b)],x_34(c)]
 =[x_12(a),[x_23(b),x_34(c)]].
```

On a `delta`-multiplicative unitary packet, the two evaluated words are at
HS distance at most `30 delta`; their normalized mean squared defect over an
arbitrarily large finite coefficient table is therefore at most
`900 delta^2`.  See
`TRUE_FOUR_ROOT_ASSOCIATIVITY_HAS_UNIFORM_HS_BUDGET.md`.

This supplies the size-uniform multiplication-coherence budget required by
the approximate bi-corepresentation route, conditional on identifying its
coproduct coefficients with these word evaluations.  The remaining gate has
two inseparable parts: assemble the raw/comb blocks into one asymptotically
unitary coefficient matrix `V`, and prove that its dual-coproduct expansion
is the averaged four-root expansion above.  An arbitrary commutant unitary in
the regular finite-envelope model preserves the group words but defeats that
identification.  Table cardinality produces no further loss; coefficient
identification remains substantive.

## 2026-08-14 closed: perfect no-signaling labels are still not whole maps

For every perfect binary pairing of size `N>=4`, let `q_c` be uniform on the
nonzero output pairs with pairing value `c`.  Each marginal of both `q_0`
and `q_1` is uniform on the nonzero labels.  Therefore the two diagonal
contexts can use `q_(b(v,w))` and the crossed context can use `q_0`: all
three pairing requirements hold exactly and all shared endpoint marginals
match.  See `FALSE_NONSIGNALING_PAIRED_QUOTIENT_SHORTCUT.md`.

This exact countermodel proves that no-signaling label PVMs, even with zero
pairing error, cannot replace a law on whole response maps.  Generic
Walsh--Hadamard rigidity does not fix the issue either: Hadamard matrices of
size at least four possess nonclassical quantum symmetries; see
`FALSE_HADAMARD_QUANTUM_SYMMETRY_CLASSICALIZATION.md`.  Do not spend further
effort on marginal/tree arguments or automatic classicality of the pairing
table.  The shortest live route is now the special atlas statement that the
raw branch decoder is constant on the comb compressor's extension-character
fibers, forced by cross-root multiplication.

This fiber statement now has a single quantitative target.  Let `B` be the
raw binary branch projection and `A_Y` the coarse source-character algebra.
Fiberwise majority decoding and conditional-variance arithmetic give

```text
decoder error <= 2 ||B-E_{A_Y}(B)||_2^2.
```

See `TRUE_BINARY_EXTENSION_FIBER_MAJORITY_DECODER.md` and the source-level
formalization in `Leavitt/FiniteBinaryFiberDecoder.lean`.  Search for one
cross-root word proving `B` is asymptotically in `A_Y`; that estimate now
subsumes the entire binary fiber-decoder step.

For the fixed Pauli carrier, orientation can be discarded altogether.  Put
`E=PQ` and `F=U*QU`, with traces `1/8` and `1/4`.  The squared distance of
`F` from `W*(E)=span{E,1-E}` is always at least `3/28`.  Hence the shortest
Pauli endpoint is now binary-algebra membership

```text
dist_2(F,W*(E)) -> 0,
```

not the stronger containment `F<=E`.  See
`TRUE_PAULI_CARRIER_BINARY_ALGEBRA_GAP.md`.  The live word search may forget
which parent sheet is selected and only force vanishing conditional
variance.

The archived parent-cell audit sharpens this further.  The raw order-16 cell
containing `E` has trivial intersection with its comb conjugate containing
`F`, so `tau(EF)=1/32`.  Hence the binary expectation of `F` is exactly
`(1/4)1` and

```text
||F-(1/4)1||_2^2=3/16.
```

For arbitrary binary coefficients `a,b`, the stronger completed-square
identity is

```text
||F-(aE+b(1-E))||_2^2
 =3/16+(1/8)(a-1/4)^2+(7/8)(b-1/4)^2.
```

Thus the minimal Pauli recovery gate is still
`dist_2(F,W*(E))->0`; the canonical moment then forces the best coefficients
to be `1/4,1/4` and yields the scalar formulation `F -> (1/4)1`.  Scalar
collapse is a consequence, not an independently justified shortcut.  No
overlap parameter or orientation choice remains in the terminal
contradiction.

The binary residual itself now splits orthogonally into Pauli parity and
within-sheet multiplicity variance.  If `y=tau(EFEF)>=0`, then for the
canonical packet

```text
parity defect       =1/16-2y,
multiplicity defect =1/8+2y.
```

Thus the multiplicity defect alone is always at least `1/8`.  Merely forcing
the transported carrier to commute with the parent Pauli sign cannot finish
the argument; the next relation must scalarize the two multiplicity-valued
diagonal blocks.  See
`TRUE_PAULI_BINARY_GAP_IS_MULTIPLICITY_VARIANCE.md`.

## 2026-08-13 robust paired quotient: a direct `1/36` Hamming floor

A perfect finite binary pairing turns the two diagonal transport relations
into an automatic permutation-repair theorem.  If their mismatch rates are
`eps00,eps11` and the crossed-zero mismatch rate is `eps01`, then

```text
eps01 + 4 eps00 + 4 eps11 >= (N-1)/(2N),
max(eps01,eps00,eps11) >= 1/36.
```

The proof counts collisions in the fibers of the two diagonal maps: two
distinct rows of a perfect binary pairing differ on exactly half the labels,
so a diagonal map with error `eps` is within Hamming distance `4 eps` of a
permutation.  The repaired crossed table has one-density `(N-1)/(2N)`.
See `TRUE_ROBUST_PAIRED_QUOTIENT_HAMMING_FLOOR.md`.

This removes the post-extraction requirements of a complex Fourier unitary,
near-bijectivity, deletion of trivial modes, and invariant spectral
truncation.  The live gate is common-coordinate extraction of the finite
perfect-pairing labels plus a **common classical latent-map lift** of
the three observed transport couplings.  Four separate bistochastic
block-mass marginals do not suffice: multiplying those marginals silently
assumes independence.  See
`FALSE_INDEPENDENT_BISTOCHASTIC_KERNEL_EXTRACTION.md`.

The three contexts form the tree `L0--R0--L1--R1`.  Hence compatible
classical pair-laws on whole maps glue automatically; see
`TRUE_TREE_GLUE_COMMON_TRANSPORT_LAWS.md`.  The remaining hard step is
pairwise classicalization of the normalized-HS four-index correlations while
matching the shared `R0` and `L1` marginals.  It is not a four-way Birkhoff
synchronization problem.

The smallest operator form of that step is now explicit.  Edgewise commuting
PVMs indexed by **whole response maps** give the three pair-laws by trace and
match the shared marginals automatically.  See
`TRUE_EDGE_PVM_LOCALITY_CRITERION.md`.  The Pauli packet supplies label PVMs,
not these whole-map PVMs; producing the latter is the live use of the raw
compressor and Kazhdan chart restrictions.

The growing number of whole-map outcomes creates no further simultaneous
rounding problem. If the three path-edge total commutator energies tend to
zero, blockwise POVM orthogonalization repairs the PVMs successively along
`L0--R0--L1--R1`, with universal constants and no alphabet loss. For exact
finite abelian root representations, the total spectral-PVM commutator
energy is exactly the subgroup-averaged unitary commutator defect by
operator-valued Parseval. See
`TRUE_PATH_PVMS_CLASSICALIZE_WITHOUT_OUTCOME_LOSS.md`. The live input is
therefore the multiplication-coherent decoder together with its three total
edge energies, not an abstract growing-family PVM rounding theorem.

There is also a sufficient pre-rounding criterion for those edge energies.
If two transition POVMs are compressions `P E_i P` and `P F_j P` of target
character PVMs through one common source cut, their total commutator energy
is bounded by the target-PVM commutator energy plus the two total leakage
energies. Separate cardinality-free POVM rounding preserves this conclusion.
See `TRUE_COMMUTING_TARGET_PACKETS_SYNCHRONIZE_TRANSITIONS.md`. Hence a
commuting distant-root placement for each of the three path contexts would
close the analytic compatibility step; the remaining audit is whether the
raw/four-root routing actually supplies those placements together with the
correct multiplication decoder.

The required placement exists algebraically. Put the two variable packets
on the outer roots `x_12(a t_i)` and `x_34(s_j b)`. They commute exactly, but
the fixed middle root `x_23(1)` gives

```text
[x_12(a t_i),[x_23(1),x_34(s_j b)]]
 =x_14(delta_ij a b).
```

See `TRUE_COMMUTING_OUTER_ROOTS_RETAIN_LEAVITT_TABLE.md` and
`Leavitt/OuterRootLeavittRouting.lean`. The live compatibility theorem is
not carrier alignment: `x_14(1)` commutes with both outer packets and the
middle root, so its nontrivial spectral corner is automatically common and
has positive trace. The remaining statement is proper-compressor decoding:
show that the outer transition blocks become deterministic response maps on
that carrier and that the nested word decodes their long-root character with
vanishing total mismatch. The finite `UT_4(F_2)` regular model proves that
the local nested table alone cannot supply this decoder. See
`TRUE_LONG_ROOT_CARRIER_IS_COMMON_BUT_NOT_A_DECODER.md`.

The two outer transitions need not be synchronized after the fact. In rank
five the four-root chain lies inside the rank-four core, and the same comb
compressor implements `alpha` on both commuting outer root groups. Apply
finite-group exactification and covariance to their product group. This
produces one joint extension-character PVM, with the two outer measurements
as commuting marginals and total rounding error below
`9(e_L+e_R)^2`. See
`TRUE_ONE_COMPRESSOR_JOINTLY_RECOVERS_BOTH_OUTER_TRANSITIONS.md`. The live
gate is therefore only the finite-window endomorphism decoder for the four
one-sided Leavitt maps, not joint transition-PVM recovery.

The raw swap itself now supplies the complete local branch decoder: it fixes
the `s0`/`t0` adjacent roots and routes the `s1`/`t1` roots to the last
coordinate, while their Steinberg commutators give the full
`t_l s_k=delta_lk` table.  See `TRUE_RAW_SWAP_FULL_BRANCH_ROUTING.md`.
Therefore the live theorem is narrower still: synchronize that already
deterministic branch label with the many-to-one extension fibers of the comb
compressor.  Searching for another local cross-zero commutator inside the
finite Pauli packet is dead work.

Do not apply this directly to the four raw `C2^2` cuts.  Their conditioned
comb transition matrix is the uniform `1/4` kernel, so it is maximally far
from the required diagonal transports.  The labels must be the deeper
paired-radical multiplication labels.

## 2026-08-13 finite paired endpoint is formalized

The paired-radical quotient contradiction now has a basis-free, kernel-checked
finite form.  A nonempty pairing separating points on both sides cannot carry
the two diagonal transports and the crossed-zero transport: the diagonal
identities make `R0` and `L1` injective, finiteness makes them surjective, and
the cross identity then annihilates every pair.  See
`TRUE_FINITE_PAIRED_QUOTIENT_OBSTRUCTION.md` and
`Leavitt/FinitePairedQuotientObstruction.lean`.

This sharpens the analytic target.  Recovering the entire coefficient ring is
unnecessary; it suffices to recover two finite separating quotients, the two
diagonal transport pairs, and one crossed-zero pair in common finite
multiplicity coordinates.  The construction of those quotients from
normalized-HS microstates remains open.

## 2026-08-13 all-depth hard-packet quotient and the live holonomy

The hard `11/30` pairs preserve a common three-dimensional eventual-zero
path sector.  On it every recovered parent equals its `0` child while the
`1` child vanishes.  This gives an all-depth finite star representation
which forbids a complementary-child equivalence in the algebra generated by
all six hard pairs; see `FALSE_HARD_PACKET_EVENTUAL_ZERO_GERM.md`.

The completed raw and comb compressor elements also act trivially on this
quotient, although four of six distinct raw source syllables and eleven of
28 comb syllables leave it before the product returns.  This does not refute
the existing properly infinite packet: its parent `p_11` is zero in the germ
quotient.  The result closes deeper hard-only searches.  The live theorem is
still finite-multiplicity recovery of `p_11,p_001` and the completed
compressor corners; intermediate source-prefix holonomy is one possible
recovery mechanism.

## 2026-08-13 closed: alternating finite Reynolds loses the fingerprint

The exact alternating expectation `E_A E_(P')` on the four coefficient cuts
plus `1-q` has spectrum

```text
1, 19/64, 11/64, 11/64, 1/16.
```

See `FALSE_ALTERNATING_REYNOLDS_CONTRACTS_COEFFICIENT_SIGNAL.md`; the
diagonalization is Lean-checked.  Its only fixed vector is the scalar
identity, and every centered coefficient mode contracts to at most
`19/64` of its norm per iteration.  Do not try to obtain alignment by alternating the
separately recovered finite packet expectations.  The `11/64` fingerprint
is useful only after a genuinely simultaneous nonfinite reconstruction has
already been supplied.

## 2026-08-13 explicit graded escape: `h=[U*X_1U,raw]`

The exceptional mixed commutator from the packet scan has infinite order,
not merely undetected bounded order.  Its unique least-degree Leavitt term is

```text
s_00 t_(00(10)^4),
```

so `h^n` has unique least-degree term
`s_00 t_(00(10)^(4n))` and degree `-8n`.  See
`TRUE_MIXED_COMMUTATOR_HAS_INFINITE_ORDER.md`.

This is the smallest concrete cross-chart axis on which to search for the
missing multiplication module.  Its first sixteen nontrivial translates of
the top coefficient cut have overlap `1/64=tau(F)^2`, not zero.  Therefore
do not pursue a wandering-projection proof from `h` alone.  Moreover both
packet involutions conjugate `h` to `h^(-1)`, a generic identity Lean-checked
in `Sofic/MixedCommutatorDihedral.lean`.  The raw relations explicitly retain
both directions.  A one-sided leakage module would need a further
non-invariant coefficient/spectral compression; it does not come from this
dihedral subgroup itself.

## 2026-08-13 live mixed direction: orbit fingerprint and `[X'_1,raw]`

The transported order-32 Pauli packet has only an order-2 pointwise
stabilizer of the raw coefficient `C^4`.  Nevertheless its 16-cut orbit
average retains the asymmetric raw expectation weights

```text
75/256, 31/256, 15/256, 15/256.
```

The top raw cut is canonically recovered by a quadratic polynomial with gap
`11/64`; see `TRUE_TRANSPORTED_PAULI_ORBIT_FINGERPRINT.md` and the Lean theorem
`recover_top_cut_from_pauli_orbit_fingerprint`.  Use this polynomial to kill
permutation/gauge ambiguity after any simultaneous reconstruction.  It does
not create the reconstruction or put a transported cut in the raw space.

Among commutators of the five transported packet generators with `raw`, four
have order 2 while `[X'_1,raw]` has infinite order by the graded argument
above.  Its dihedral symmetry rules out a direct one-sided module.  Do not
return to common-finite-subgroup averaging: the full raw/comb intersection is
trivial and the orbit residual from the raw coefficient space is positive.

## 2026-08-13 closed shortcut: no common raw/comb finite subgroup

The full raw packet `K=<X0,X1,Z0,Z1,raw>` has order `512`, but

```text
K intersect U* K U = 1.
```

See `FALSE_RAW_512_COMB_INTERSECTION_IS_TRIVIAL.md` and its bounded exact
certificate.  Do not attempt to derive coefficient-space membership by
Reynolds averaging a common finite subgroup.  The remaining proof must use a
cross-chart kernel relator which constrains the relative multiplicity unitary,
or directly recover the paired multiplication module.

## 2026-08-13 weakest terminal gate: coefficient-space membership

Let `A_0` be the span of the four raw coefficient cuts and `q` their sum.
For every transported cut `G`, exact trace-flatness makes its orthogonal
projection onto `A_0` equal to `q/8`, with

```text
||G-q/8||_2^2=15/128.
```

See `TRUE_COEFFICIENT_EXPECTATION_GAP.md`; the matrix identity is Lean-checked.
The shortest sufficient theorem is therefore: simultaneous finite-coordinate
recovery places one transported cut at `o(1)` distance from the raw
coefficient space.  This is weaker than algebra equality or permutation
alignment, and should be attempted first.  It is still not a consequence of
generic Reynolds averaging.

## 2026-08-13 audit: generic Reynolds recovery is insufficient

Do not claim the `C^4` alignment from the existing Kazhdan or finite-normal
corner files.  The relative comb implementer retains a fixed Reynolds norm
deficit, so it is not an already-commuting ultraproduct element.  See
`FALSE_EXISTING_REYNOLDS_DOES_NOT_ALIGN_COEFFICIENT_C4.md`.

The sufficient new theorem is simultaneous and comb-compatible: recover both
four-cut multiplicity algebras in the same finite coordinates and match one
transported cut to one raw cut with squared HS error below `1/8`.  The exact
trace moments force every such squared distance to tend to `7/32`, giving a
strict contradiction.  This is the precise closure gate; generic commutant
lifting or separate finite-packet exactification does not close it.

## 2026-08-13 spectral fallback: only invariance remains

For any trace-flat coefficient block, `H=FGF` is a positive contraction with
support trace `1/8` and total trace `1/64`.  Its spectral cut above `1/16`
has trace at least `1/120`, and the retained transition has singular values
at least `1/4`.  See `TRUE_TRACE_FLAT_BLOCK_SPECTRAL_FLOOR.md`; the arithmetic
constant is Lean-checked.

Spectral coarea removes the need to postulate that invariance separately.
If the four recovered arrows are contractions and
`||[H,A_k]||_2->0`, averaging the cuts `1_[t,infinity)(H)` over
`t in [1/32,1/16]` selects one common coordinate-dependent cut of trace at
least `1/120`, with singular values at least `1/sqrt(32)`, whose two-sided
leakage under all four arrows tends to zero.  See
`TRUE_SPECTRAL_COAREA_INVARIANT_CUT.md`.  Therefore the reduced-Fourier
fallback now needs only the four polynomial commutator estimates
`||[FGF,A_k]||_2->0`.  The direct `C^4` alignment gate below remains shorter;
use this route if exact algebra alignment is too strong.

Those commutator estimates themselves follow from the natural transition
intertwinings.  Put `T=GF`, and let `A_k,B_k` be the source and target
coefficient arrows.  The dimension-free Gram estimate

```text
||[T* T,A_k]||_2 <=2||T A_k-B_k T||_2
```

shows that it is enough to prove

```text
||GF A_k-B_k GF||_2->0,       k=1,...,4.
```

Combined with coarea, these four errors give a common cut `P` of trace at
least `1/120` and

```text
sum_k ||[P,A_k]||_2^2
 <=64 sum_k ||GF A_k-B_k GF||_2.
```

See `TRUE_TRANSITION_INTERTWINING_CONTROLS_SPECTRAL_LEAKAGE.md`.  This is now
the smallest spectral fallback gate: it is phrased entirely in the
cross-chart multiplication-module transport which the group packet is
supposed to encode.

If the recovered arrows are contractions rather than coordinate unitaries,
use the exact two-sided identity

```text
[T* T,A]=T*(T A-B T)+(T* B-A T*)T.
```

It is then enough to prove both

```text
||T A_k-B_k T||_2->0,
||T* B_k-A_k T*||_2->0.
```

This distinction matters: the first one-sided estimate uses unitarity of
the coordinate shifts, whereas the Leavitt coefficient arrows are only
contractions.  The two-sided version is formalized as
`hsNormSq_transitionGram_commutator_le_two_sided` and makes no unitary
assumption on `A_k,B_k`.

The four-arrow family can be reduced further.  In the terminal products

```text
R0 S0=I,       R1 S1=I,       R0 S1=0,
```

inserting a carrier projection produces only the errors

```text
P Ri(1-P)SjP,              i=0,1.
```

Thus only `R0,R1` need to almost preserve the coarea cut.  If `eta` is the
maximum of the three compressed ambient product defects and `lambda` is the
maximum of `||P R_i(1-P)||_2`, the trace-`alpha` corner theorem gives

```text
eta+lambda>=sqrt(alpha)(2-sqrt(3)).
```

Since `alpha>=1/120`, the ambient floor is
`(2-sqrt(3))/sqrt(120)`.  See
`TRUE_TWO_LEFT_ARROWS_SUFFICE_FOR_SPECTRAL_LEAVITT.md`.  The smallest
spectral gate is consequently two forward/reverse transition pairs, not
four-arrow invariance.

There is a choice of which two.  The insertion error for an edge `Ri Sj` is
bounded by either endpoint leakage, so the problem is the minimum vertex
cover of

```text
(R0,S0),       (R1,S1),       (R0,S1).
```

The crossed pair `{R0,S1}` is a size-two cover and matches the exact finite
paired-quotient proof: the two diagonal relations make these two maps
bijective, and their crossed relation is zero.  Prioritize synchronization
of `R0,S1`; it unifies the spectral and radical-quotient routes and avoids
recovering either unused arrow's invariant cut.

For the reduced pairing formulation there is an even better choice: the
right-factor cover `{L0,L1}`.  No unitary repair is needed.  If `W,R,L` are
contractions and `eta=||R* W L-W||_2`, contraction mass saturation gives

```text
||W L-R W||_2,
||W*R-LW*||_2 <=eta+sqrt(2 eta),

||[W*W,L]||_2 <=2 eta+2 sqrt(2 eta).
```

Therefore the two diagonal relations already supply the two coarea
commutators, while `{L0,L1}` covers all three products.  See
`TRUE_DIAGONAL_PAIRING_DEFECT_SUPPLIES_SPECTRAL_INVARIANCE.md`.  After
common-coordinate extraction, spectral invariance is not an additional
gate; the only remaining analytic input is the three pairing defects
themselves.

## 2026-08-13 sharp terminal gate: align two `C^4` coefficient algebras

For every raw coefficient character cut `F_epsilon` and every transported cut
`G_eta=U*F_eta U`, the exact trace table gives

```text
||F_epsilon-G_eta||_2^2=7/32.
```

See `TRUE_DOUBLE_PAULI_COMB_ANTINORMALIZER_GAP.md`; the projection-distance
identity and the constant are Lean-checked.  Since every automorphism of
`C^4` permutes its minimal cuts, a comb-compatible coordinate recovery which
aligns the raw and transported finite-multiplicity coefficient algebras gives
an immediate contradiction.

This is now the shortest terminal theorem to target.  Prove simultaneous
matrix-coordinate recovery of the two `C^4` coefficient algebras and their
comb covariance, with `o(1)` loss.  It is stronger than recovering one
ultraproduct commutant and is false in arbitrary finite von Neumann algebras;
its justification must use finite matrix coordinates and the two Kazhdan
chart restrictions.  If this alignment cannot be obtained, fall back to the
one-sided spectral-truncation formulation below.

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
> strategies, and construct a bespoke finite two-player torically determined
> game preserving those two properties and whose scalar phase survives the
> normal closure of its clauses.

No efficient or uniform compiler is sought.  Only this one source algebra has
to be torically groupified.  A finite LCS game is a sufficient specialization,
but `TRUE_NORMAL_TORIC_GAP_IMPLIES_NONHYPERLINEAR.md` proves that full LCS
syntax is not necessary.

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

The broader target is a finite two-player torically determined game `T_0`
with finite scalar phase group `B`.  In the augmented universal group

```text
Gtilde=B times G,
```

let `N` be the normal closure of its toric clauses.  Construct `T_0` and
constants \(c,C>0\) with:

1. **exact completeness:** every perfect commuting strategy for \(B_0\)
   induces a perfect commuting strategy for `T_0`;
2. **robust soundness:** a finite-dimensional strategy for `T_0` of defect
   \(\delta\) induces a finite-dimensional strategy for \(B_0\) of defect at
   most \(C\delta^c\); and
3. **phase-safe normal closure:** `N intersect B={1}`.

For item 3 it is enough that the perfect target representation be tracial on
the full toric universal group: its trace kernel is normal, contains every
clause, and cannot contain a nontrivial element of the faithfully represented
scalar phase group.

Then

\[
\omega_{qc}(T_0)=1,
\qquad
\omega_{qa}(T_0)<1.
\tag{HL2}
\]

The phase-safe toric theorem then makes the finitely presented quotient
`Gtilde/N` nonhyperlinear.  If `T_0` is an LCS game, this recovers the usual
solution-group endpoint.

### The sufficient LCS specialization is profile-free

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
the LCS specialization is the existence of `(HL2a)`, not conversion of such
an instance to a nonhyperlinear group.  The phase-safe toric theorem proves
the analogous final implication for the broader target without requiring an
approximate-representation decoder.  This is also why the `epsilon=0`
endpoint in Taller--Vidick is exactly the group-theoretic open problem.

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

### Gate 2: exact toric embedding test

Attempt to encode the source determining relations by scalar monomial clauses
in a finite universal game group, with the source partition and
forbidden-product relations holding identically.  Simultaneously track the
normal closure of the clauses and require its intersection with the finite
phase group to be trivial.  This is an exact finite word problem.  The first
search should allow auxiliary questions, answers, variables, and equations
freely; efficiency and size do not matter.

Kill the route immediately if a representation-theoretic invariant of the
specific \(B_0\) rules out every such encoding.  The generic obstruction is
not enough.

### Gate 3: robust reverse decoding

For a candidate exact encoding, prove a decoding estimate from near-perfect
finite-dimensional toric strategies back to near-perfect \(B_0\) strategies.
Use:

* HS stability of projection and involution relations;
* local commutativity gadgets;
* Paddock's dimension-independent BCS strategy/approximate-representation
  correspondence;
* finite telescoping only.

This gate must be dimension independent.  No bounded-dimension scan is a
substitute.

### Gate 4: phase-safe quotient extraction

Once `(HL2)` and phase survival are certified, write down the finite
presentation of `Gtilde/N`.  The central phase character corner gives the
final nonhyperlinearity proof.  No separate uniform invisibility estimate for
arbitrary matrix representations is required.

## Full-packet one-symmetry form of the atlas multiplicity gate

The archived trivial-intersection certificate for the raw packet `K` and its
comb conjugate `K'` gives the exact full-algebra expectation

```text
E_(C[K])(F)=(1/4)1,
dist_2(F,C[K])^2=3/16.
```

Haar averaging over the coordinate commutant of the exactified copy of `K`
therefore gives one unitary `V_n` with

```text
[V_n,Alg(rho_n(K))]=0,
||[V_n,F_n]||_2^2 >= 3/8-o(1).
```

A two-by-two dilation makes `V_n` a self-adjoint involution without changing
the energy. This strictly strengthens the earlier binary-cut witness: the
chosen symmetry respects every raw Pauli-packet element, not just the parent
projection. Thus the terminal theorem only has to force the transported
carrier to commute with all coordinate unitaries in the full raw-packet
commutant. The coordinate dependence remains the gate and cannot be replaced
by a fixed group word. See
`TRUE_FULL_RAW_PACKET_COMMUTANT_WITNESS.md`.

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
