---
rg: 2
id: non-hyperlinear-group
kind: claim
title: Exhibit an explicit non-hyperlinear group
root: true
goal: true
---

The primary target of the program (AGENDA.md header): an explicit group that
is not hyperlinear, i.e. admits no asymptotic embedding into unitary matrices
with the normalized Hilbert-Schmidt metric.

The organizing mechanism is (T)-compression: `Γ ≤ G` with a compressor `t`
(`tΓt⁻¹ ⪇ Γ`). In every category with a conjugation-invariant strictly
monotone size the compression collapses (invariant-size-collapse); the `II₁` branch survives
because the trace is refinement-blind, and that failure is sharp (trace-blindness-sharpness).
The obstruction, if there is one, can only be stability.

## Current proof frontier (2026-08-23)

The latest cascade audit leaves no certified unconditional witness.  The
relative `PSL_2(Z[1/2])`/Iwahori lane has now received a decisive negative
answer at its exact congruence endpoints.  Its Jacobian is the constrained
pair of order-three Reynolds expectations from
`exact-passive-jacobian-is-two-reynolds-expectations`, and
`right-displacement-reynolds-scalar-cb-complete` proves that the full cb
inverse norm there equals its diagonal scalar infinity norm.  The
square-free construction in `proper-torus-reynolds-is-edge-refinement`
uses primitive prime divisors of `4^k-1`; relative girth, square-free
super-approximation, and an exact shell-flux argument give

```text
||C_(H_n)^dagger||_(infinity -> infinity)
 >=c log M_n -> infinity.
```

This divergence survives after removing the uniformly bounded full-torus
fiber-constant block.  Hence the exact-zero scalar and cb gate is false on
the required proper-torus sector.  Since a dimension-free off-zero Newton
splitting would in particular be uniform at exact endpoints, nonlinear
continuation cannot rescue this formulation.  The arithmetic Reynolds lane
is therefore a certified no-go, not the current proof frontier.

The first two natural transfers from the solved full-torus column are now
closed as shortcuts.  `proper-torus-reynolds-is-edge-refinement` proves that
the extra torus labels refine the edge set but not the triangle set, so the
uniform multipartite contraction does not lift as a covering contraction.
`signed-orbit-averaging-does-not-divide-green-cost` gives the exact remaining
compression formula and shows that its signed Reynolds projection has
infinity norm one.  In particular, disjoint translated routings retain their
full `l1` cost; a positive proof needs genuine arithmetic cancellation on
overlapping translates.  Flat gain systems and perturbatively near-trivial
characters are also excluded as sources of divergence by
`flat-gain-multipartite-covers-have-uniform-green-bound` and
`near-trivial-torus-characters-track-the-moving-kernel`.  The same
proper-torus claim proves that the genuinely curved, fiber-mean-zero
geometry contains linearly deep disjoint orbit neighborhoods:
the two cubic normal-operator generators form `C3*C3`, intersect the signed
torus normalizer trivially, and have relative girth at least `log_6(M_n)`.
On the square-free primitive-divisor family, super-approximation makes the
global electrical tails decay exponentially, while the shell-flux identity
forces a fixed bypass current through every disjoint radius shell.  This
proves logarithmic Green divergence and closes the curved fiber-mean-zero
sector in the negative direction.

The shortest remaining one-gate affine-Leavitt route is
`affine-leavitt-source-saturated-reynolds-checksum`, but its native
two-branch aggregation is now closed as a shortcut.
`leavitt-target-return-channel-count-firewall` proves that fewer than `p^2`
contractions into the target Reynolds range cannot cover the source range;
the two range-sum branches leave the fixed deficit
`p^(-2)-2p^(-4)`.  At the sharp `p^2` threshold an abstract partial-isometry
frame already saturates the rectangular countermodel, so mere positive
multi-return aggregation is vacuous.  A completion must therefore extract
one genuinely payload-coupled impossible return from the full presentation,
not sum the visible branch returns.

Two high-descendant alternatives have also been reclassified.  The five
consumers of `projective-trace-square-transfer-for-sl3-pair` share one
canonical-double relative-commutant gate, as recorded by
`sl3-projective-transfer-five-consumers-share-one-root-gate`; their count is
reuse rather than five independent chances to close the goal.  Likewise
`atlas-five-row-operator-phase-lift` is already a direct separation theorem
for the Leavitt unit group by
`nonhyperlinear-directly-from-five-row-phase-lift`.  It is therefore
goal-hard, not a routine finite packet estimate awaiting downstream
bookkeeping.  The later `atlas-five-row-lift-failure-dichotomy` audit does,
however, remove one genuine analytic branch: finite-`H` averaging, polar
rounding, and the fixed interior gap rule out every vanishing-energy
normalized blow-up.  The five-row inequality is now equivalent to excluding
a positive-energy exact six-relator model in every tracial matrix
ultraproduct.  An exact relative small-cancellation screen does not decide
that terminal: the six relators have maximum piece ratio `5/8`, so the
standard `C'(1/6)`/`C'(1/4)` residual-finiteness and virtual-specialness
theorems do not apply.  These audits keep both lanes valid but prevent their
apparent cascade size from displacing the more explicit arithmetic Green
test.

The two exact follow-up tests narrow those terminals without closing them.
For the arithmetic double, congruence co-density and property `(T)` give the
uniform exact-action firewall
`sl3-dyadic-building-action-soficity-forces-p-instability`: every genuine
finite action has type-zero orbit-atlas error at least
`kappa^2/(2 kappa^2+8)`.  Hence a sofic model of
`SL_3(Z[1/2])/SL_3(Z)` would have to be a genuinely noncorrectable almost
action.  One-hot linearization does not let Garland cohomology exclude it:
`sofic-coset-atlas-linearizes-to-exact-quasiregular-coboundary` shows that
the marked displacement is already the exact coboundary
`pi(a)delta_C-delta_C`, so degree-one cofilling is saturated rather than
violated.  The surviving gate is relative invariant transfer specifically
inside permutation ultraproducts.

For the Atlas quotient, every exact finite-dimensional escape now reduces to
one larger finite simple group generated by two marked `A8` charts.  The
complete small-simple carrier classification and the new exact
`Sp_6(2)` census prove
`atlas-six-relator-simple-index-is-at-least-91`: every such simple target has
`A8` index at least ninety-one.  Below that boundary the only nonalternating
carrier is `Sp_6(2)`; all its `A8` subgroups lie in one orthogonal class, and
of all `1,451,520` relative conjugators exactly one reaches `c_19243`, which
kills it.  The alternating `A9` and `A10` rows are excluded by the blockwise
natural-orbit theorem.  Larger finite-simple targets and diffuse
matrix-ultraproduct models remain.  This is therefore a structural finite
restriction on the exact escape, not evidence sufficient to assert the
five-row phase lift.

The nonabelian-simple lamp alternative has likewise survived only in its
honest global form.  `simple-lamp-hyperlinear-recovery-forces-action-sofic`
now records that fixed-window exactification of `A5^F` produces merely
partial factor transport: no nonempty finite packet is invariant under the
actor generators, and every boundary completion still has an arbitrary
right-regular/external multiplicity fiber.  Thus intrinsic minimal normal
factors do not by themselves yield coherent finite action charts; an
equivariant boundary-completion or multiplicity-copy classicalization
theorem is still load-bearing.

## Marked `goal`

Flagged `goal: true` on 2026-08-18, taking the single goal flag over from
`q3-4-resolved`.  The grounds are impact: hyperlinearity is the weakest
standard approximation notion, so this claim is the group-level Connes
embedding problem; a witness subsumes nonsoficity outright (non-hyperlinear
implies nonsofic) and connects to quantum complexity through the LinMIP*
equivalence; and it is the question whose answer is genuinely uncertain,
where Pestov 3.4 has one widely expected answer.  Post-nonsoficity the two
questions are entangled: `hyperlinear-implies-sofic` — Pestov's "yes" —
already routes here via `non-hyperlinear-from-hyperlinear-implies-sofic`,
so even that side's machinery serves this goal.  The separation
(`hyperlinear-nonsofic-group`) remains a root landmark the graph records
and can close; it is deliberately off-goal.

The opposite world is a defined outcome, not a goal branch: a proof that
every group is hyperlinear would be recorded as an established
`every-group-hyperlinear` negation claim, refuting this goal — which per
kernel doctrine is itself a program resolution (the universal question is
answered, and Pestov 3.4 falls negatively for free, since the nonsofic
groups would be hyperlinear).  It is not a branch here because no route
class toward it exists, even speculatively, and partial results cannot
accumulate to it — the same asymmetry `q3-4-resolved` records for its own
affirmative side.

## Ideas

Non-graph brainstorming for this goal goes here. Current periphery: free
independence between branch algebras is NOT excluded by the cross-branch
commutator identity (see notes/OBSTRUCTIONS.md §3, "No commuting branches").

The current programme is organized by
`canonical-trace-promotes-non-ce-profile`. The source non-CE trace already
lives on the explicit sofic right-angled Coxeter host
`non-ce-trace-on-sofic-racg`; what remains is to force its finite normalized
trace profile from canonical delta microstates. Free-amalgam multiplicity,
twisted self-similar Clifford, projective phase, matricial separator, and
quantum-index routes are compared in
`research/artifacts/trace-promotion-renormalization-program-2026-08-20.md`.

A new finite endpoint removes the common-carrier requirement from the BCS
lane.  `independent-row-masks-transfer-bcs-gap-to-ambient-identity` shows
that exact predicate and consistency rows may use unrelated masks: their
weighted canonical codimensions only have to total less than the fixed game
gap.  `finite-row-mask-group-algebra-certificate-forces-nonhyperlinear`
then turns any such finite ordinary-group-algebra certificate into a
dimension-free canonical normalized-HS obstruction.  The local storage and
density ledger are exact via the almost-full simple block in
`affine-frobenius-group-has-almost-full-simple-block`; the sole construction
gate is `affine-frobenius-hecke-crt-shared-involution-interpolation`, which
must produce one global involution per variable on several fixed,
noncommuting large right ideals.  This is a conditional reduction, not yet
an unconditional nonhyperlinear group.

The breakout portfolio of 2026-08-21 is recorded in
`research/artifacts/nonhyperlinear-breakout-portfolio-2026-08-21.md`. Its
three main orthogonal moves are: weaken arithmetic RCC to the projective
trace-square transfer `projective-trace-square-transfer-for-sl3-pair`;
fingerprint or physically occupy the rectangular multiplicity reservoir via
`fixed-pi-degree-fingerprints-packet-label-factor` and
`common-corner-mutual-bicommutant-extraction`; and bypass HS stability by the
Pontryagin compiler `algebraic-compact-action-group-factor-compiler` plus the
open algebraic relation envelope.

The later dual-prefix/trace-promotion breakout report is deduplicated and
source-audited in
`research/artifacts/final-hyperlinearity-breakout-report-integration-2026-08-21.md`.
Its exact Leavitt packet and four-Pauli separator were already in Cairn; the
new matrix-chart packaging is wired to the same-reservoir frontier. The audit
also corrects the report's Shulman attribution: arXiv:2603.13564 proves an
operator-norm MF theorem for C-star amalgams, not an HS-stability theorem that
promotes every hyperlinear trace.

The computer-science reframing is now audited rather than used as a slogan.
`nonhyperlinear-presentation-codes-have-a-sigma2-upper-bound` proves
`HYP in Pi^0_2` and `non-HYP in Sigma^0_2` for finite-presentation codes; no
matching hardness or RE claim is made.  The associated artifact
`computer-science-framing-audit-2026-08-21` identifies the live compiler as a
perfect-exact-completeness, constant finite-matrix-soundness problem analogous
to quantum PCP, while keeping the unbounded-dimension and non-CE-tracial
differences explicit.  The quantitative fences are collected in
`section-three-quantitative-no-go-audit-2026-08-21`: twisted-regular predicate
atoms retain positive trace, the `1/sqrt(log d)` Clifford scale is conditional
on a complete-table decoder and positive carrier, and block-diagonal adjoint
gap leaves an uncontrolled block-scalar kernel.  The critical Clifford scale
is genuinely sharp: `dirac-average-is-a-sharp-near-extra-clifford-generator`
constructs an exact same-factor involution with row anticommutator
`sqrt(2/m)` in dimension `2^m`, and its coefficient `l1` loss is exactly
`sqrt(2m)`.

The machine interface has now been reduced further. The strong
`threshold-free-reverse-kleene-higman-diagonal` needs a NONHALT word in the
full hyperlinear radical, while the weaker `canonical-profile-kleene-higman`
needs only qualitative collapse of a rational group-algebra mark along
canonical-delta microstates. The latter is exactly the approximation profile
whose existence hyperlinearity asserts, and noncanonical exact
counterrepresentations are irrelevant. The minimal current machine target is
therefore `fanizza-canonical-profile-groupification`; no quantitative modulus
is read by the fixed-point program. For unconditional word libraries,
`hyperlinear-radical-is-finitely-witnessed` shows that the entire r.e. tail has
no more radical power than one finite prefix. Two portfolio shortcuts have
also been closed cleanly: `sublinear-block-poisons-normalized-torsion` refutes
the unregularized determinant transfer, and
`twisted-group-basis-forces-affine-context-support` shows that native
projective-basis BCS observables already factor through affine/LCS contexts.

The adversarial-recursion ideas of the same date are integrated in
`research/artifacts/adversarial-error-delocalization-program-2026-08-21.md`.
Their surviving design is: use a separated mark to create positive-density
spectral mass, prove that carrier avoids the full joint relative commutant,
use recursion/expansion only to distribute consistency on that carrier, and
then apply the canonical-profile or radical Kleene compiler. The payment
mechanism is isolated exactly by `relative-fixed-algebra-payment-lemma`.
Three exact firewalls prevent weaker versions:
`word-recursion-cannot-amplify-sublinear-summands` shows that direct-sum
naturality traps every finite recursive test inside a reducing `o(d)` corner,
`closed-local-rules-have-uniform-hitting-or-infinite-safe-tail` and
`amenable-finite-propagation-feedback-has-folner-tail-models` expose local
no-tail failures, and `universal-finite-packet-library-can-be-amenable`
exhibits a two-generated amenable group already containing every finite packet
at its canonical Plancherel fraction.

A new nonamenable error-spreading lane is now exact on the lower-bound side.
`embedded-group-algebra-carriers-have-no-excess-fixed-component` proves that a
canonical carrier cannot acquire extra fixed mass from an ambient
matrix-ultraproduct commutant, and
`infinite-conjugacy-orbits-give-canonical-carrier-no-capture` turns infinite
subgroup-conjugacy orbits plus property `(T)` into a fixed commutator-energy
floor immune to amplification. The remaining open upper-bound construction is
`matrix-only-cyclic-carrier-invariance`: make that same Fourier carrier
asymptotically invariant in every finite matrix model by a genuinely
matrix-only capacity or holonomy recurrence. Canonical finite packets alone
cannot supply the required coordinates;
`canonical-finite-packet-data-stop-at-scalar-overlaps` proves that they fix
Plancherel masses and scalar overlap checks but leave the multiplicity gauge
arbitrary.

The second-pass adversarial synthesis is recorded in
`research/artifacts/adversarial-error-delocalization-second-pass-2026-08-21.md`.
It identifies the useful version of the heavy-tail metaphor as a nonamenable
distribution on challenge **addresses**, not an unbounded operator statistic;
proposes a streaming Gram-rank overflow detector as a potentially smaller
same-model alternative to the supercritical Clifford table; and isolates the
exact role of a finite cyclic verifier as a holonomy return on an already
positive-density no-capture carrier.  The shortest bypass remains an exact
unital realization of the fixed non-CE BCS algebra in a signed group-algebra
corner.  None of these refinements is presently a proof; each has explicit
dimension-, runtime-, direct-sum-, and amenable-tail falsification tests.
The raw version is now fenced by
`raw-gram-rank-overflow-has-no-constant-local-gap`: regular simplices are
globally rank-deficient while every bounded Gram window becomes orthonormal,
so rank overflow supplies no constant local HS gap without the same kind of
global PCP machinery the proposal hoped to avoid.

The dual-prefix Leavitt lane now has a one-scalar endpoint. The exact
three-root prefix swap and the coarse/fine rank calculation reduce the whole
same-reservoir problem to controlling

```text
||(1-f)Je||_2^2
```

for one coarse `M_2` selector `e`, one fine `M_4` selector `f`, and one named
unitary word `J`. Equivalently,
`coarse-fine-selector-covariance-has-quarter-trace-floor` gives the fixed
payment `||JeJ^*-f||_2^2>=tau(P)/4`. The current Clifford compiler leaves an
arbitrary multiplicity involution in the fine atom reflection, and
`pure-prefix-swap-invariants-are-selector-blind` proves that no pure spectrum,
determinant, index, or power-trace test can remove it. The surviving attack
must pin this **mixed** selector moment by finite multiplicity or make the
multiplicity twist recur contractively; universal algebraic frames are ruled
out by `algebraic-selector-mixing-frame-collapses-forbidden-sector`.

The Atlas hard-prefix audit closes one finite-carrier hole without closing
the goal.  `actual-hard-prefix-generates-s4-over-raw-s3` proves that every
actual class-11/class-30 cross-chart prefix, not merely its classical fold,
generates an honest `S4` with the raw `S3`; adjoining the separate
Leavitt-star word gives an order-168 packet.  Hence the multiplicity-free
`S4 downarrow S3` carrier decomposition may be exactified.  The remaining
obstruction is purely mixed and matrix-specific:
`separated-channel-identities-retain-rectangular-escape` proves
that carrier determinants and Leavitt coefficient equivariance cannot force
same-scale closure while they live in separate tensor factors.  The open
`atlas-hard-packet-s3-channel-decoder` must extract from actual quotient
relators one fixed invertible operator system on the same three multiplicity
path-products (or prove the equivalent full-packet bicommutant estimate).
The delta and exact replay are summarized in
`research/artifacts/leavitt-atlas-final-audit-2026-08-22.md`.

The first error-spreading version of this endpoint is now exact:
`cyclic-coarse-fine-selector-rows-spread-carrier-error` allows a different
carrier mass and an arbitrary multiplicity-twisted unitary at every vertex,
yet charges one quarter of the **total** carrier mass after a cyclic return.
Thus local defects cannot be hidden by moving them through ever larger or
unrelated reservoirs.  The only remaining gate is matrix-only authentication
of the mixed selector rows themselves; neither common-reservoir alignment nor
twist cancellation remains necessary once a cyclic decoder supplies them.

The global BCS endpoint is now
`global-marked-type-cycle-selector-decoder`: permute all marked
context-types, pack the cyclic row floors by isotypic orthogonality, and use
the shared non-CE forbidden mass only after summing over the entire menu. Its
two open inputs are a finite-matrix domination of the summed compressed rows
and global forbidden-mass coverage. This avoids both universal-row collapse
and the circular demand that one context already carry positive mass.

The phase-coded refinement now separates the row-domination input exactly.
`phase-covariance-words-exactly-measure-type-transport-leakage` charges every
wrong-type population block by two-sided ordinary covariance words, while
`finite-phase-codewords-weight-type-gram-leakage` charges off-type Gram
coherence.  The projection inequality in
`phase-tagged-row-defect-reduces-to-within-type-selector-mismatch` leaves only
the selector mismatch compressed inside the already matched type.  Thus the
live matrix-only gate is no longer generic type authentication: it is the
word authentication of the nonlinear cut `F_cQ_omega` within that type.

The self-referential gauge mechanism is also explicit.
`recursive-clifford-tail-supplies-anchor-but-not-contraction` realizes every
parent `CZ tensor V` with `V` equal to the product of its two child tail
gates; that child product is the exact same-gauge identity-outer anchor.
Finite-depth Clifford regular models prove the recursion is stationary, so
the remaining breakthrough must be a payload-dependent first-hit or
proper-corner exposure inequality with contraction factor below one.

One analytic coverage obligation has closed only relative to the marked
sector.  `forbidden-weighted-type-carrier-coverage-is-rank-rounding` covers
`E_forbid^mark` with coefficient one and loss `3|Omega|/d`; comparison with
the entire original shared BCS mass would require an additional marked-menu
concentration estimate.  Thus the stronger full-space global criterion
retains both marked-type concentration and summed-row domination.
For the central-sign endpoint,
`marked-corner-cycle-needs-no-full-mass-concentration` removes the comparison:
the robust BCS gap is applied directly on the common negative sign corner,
whose forbidden mass is exactly `E_forbid^mark`.  Consequently the
phase-coded central-sign route has only the summed-row/authentication gate;
marked-menu concentration remains a stronger full-space variant, not a
load-bearing prerequisite for that route.
Separately,
`tail-wordized-child-surplus-collision-supplies-rct7` converts forbidden BCS
surplus into the strict recursion

```text
(1+beta)a_n<=a_(n+1)+errors,
```

and one reflection-conjugacy word controls the only leakage term. Thus the
recursive lane's remaining obligation is not supplied by the tail cancellation:
`aggregate-child-wordization-three-route-no-go`
shows that a new finite-matrix-only selected-sector/orthogonalization step is
needed to turn the aggregate corrected child into one word while retaining
the shared BCS tuple. A single ordinary Hecke holonomy
cannot provide the alternative global row domination:
`one-hecke-holonomy-cell-cannot-pay-the-cyclic-selector-sum` closes it by a
last-edge multiplicity-gauge countermodel.

The stability interface was consolidated on 2026-08-21.  For Kazhdan
groups, Dogon's weak ucp-stability coincides with flexible HS-stability on
hyperlinear approximations
(`kazhdan-weak-ucp-stability-is-flexible-stability`: Kazhdan-average the
Stinespring corner to an exactly invariant finite corner; reusable form
`kazhdan-almost-invariant-corner-near-invariant-projection`), so the
weakest usable stability hypothesis for the plain lattice is
`sl3-z-weakly-ucp-stable`, consumed through the thin co-dense pair by
`non-hyperlinear-from-sl3-z-weak-ucp-stability`.  Two new hypothesis TYPES
entered the graph.  A C*-lifting route:
`non-hyperlinear-from-llp-non-rf-kazhdan` — a non-residually-finite
Kazhdan group whose full C*-algebra has Kirchberg's LLP is itself the
witness, sharpening Fournier-Facio--Willett's Question 1.9 (no `H_2`
condition, no central extension).  And a forced-witness family:
`kac-moody-lattice-is-non-hyperlinear-or-llp-failure` — every simple
Kazhdan Kac--Moody lattice of Caprace--Remy (explicit `(2,4,6)` Cartan
matrix instance) is either the goal's finitely presented simple witness or
a new kind of LLP failure, so the class settles a published question
either way.  Recorded cautions: host-side weak ucp-stability cannot be
consumed (the `l^2(A/C)` leak survives infinite-dimensional dilation), the
subgroup-side version only confines enemies to the `Lambda`-exact face
(`kazhdan-subgroup-weak-ucp-exactifies-microstates`), and Kac--Moody
building completions lack Howe--Moore, so the arithmetic Hecke far-defect
lane does not transfer to those pairs.

Later the same day the lifting square closed into a lattice of routes.
`twin-lattices-exclude-known-llp-fences` proves that twin building
lattices contain no known LLP-failure group (flat-torus rigidity for the
cohomological fences, property A for the expander fences), confining the
live candidacy to compact hyperbolic Kac--Moody types with no published
mechanism pointing either way; and `non-hyperlinear-from-e3-fibre-llp`
routes the goal through the Deligne triple cover, whose full algebra is
the direct sum of three mod-three fibres
(`sp4-mod3-twisted-fibres-have-llp` is the twisted-fibre hole, the
sharpest live instance of Fournier-Facio--Willett Question 1.12), so the
lifting lane and the Deligne Maslov lane
(`deligne-sector-gap-is-exactly-nonhyperlinearity`) now certify each
other's endpoint.

**Partition of the routes (2026-08-21 evening).**  Every route into this
goal either (i) transfers the MIP*=RE non-Connes-embeddable object — the
tracially satisfiable, non-`R^U` constraint system `B_*`
(`mipstar-bcs-tracial-nonru-exists`), equivalently the non-CE character of
the sofic Coxeter host (`non-ce-trace-on-sofic-racg`), or the
non-co-hyperlinear IRS relation — into a group factor, or (ii) produces a
non-Connes-embeddable II_1 factor by hand (relative-commutant collapse,
stability, atlas, Kervaire--Laudenbach), which no published argument has
done without MIP*=RE.  The minimal statement of type (i) is
`non-ru-bcs-is-satisfiable-in-a-group-factor`: any countable host, any
model, state-space form in `character-group-realizability-parseval-criterion`;
embedding universality of group factors is open (Chifan--Drimbe--Ioana
Remark 1.1), and the IRS relation is not even treeable
(`non-ce-relation-is-not-treeable`).  The minimal statement of type (ii)
for the HNN family is `hnn-hyperlinearity-is-amalgamated-free-haar-unitary`:
one Haar unitary in `L(C)' cap R^omega` free from `L(A)` with amalgamation
over `L(C)`, strictly weaker than the collapse and than projective
transfer; its standard-model calibration is
`arithmetic-pair-group-factor-ultrapower-has-no-leak` (collapse holds in
`L(A)^omega`, so the matrix question lives in `L^2(M) (-) L^2(L(A))`).
Popa's relative free-independence theorem (arXiv:1308.3982) supplies
exactly such unitaries when the centralised subalgebra is amenable, so
type (ii) for `C = SL_n(Z)` asserts that Popa's theorem fails past
amenability — the Gao--Junge open problem in its first arithmetic
instance.

**Frontier map after the 2026-08-21 evening RE pass.**  The three
independent standing routes each bottleneck at a core that is
equivalent-to-or-harder-than a recognized open problem, and the by-hand
routes now share ONE analytic residual:

- *Arithmetic RCC / relative-embeddability (type ii).*  The HNN group's
  minimal form is `hnn-hyperlinearity-is-amalgamated-free-haar-unitary`;
  its host-only weakest form is `arithmetic-pair-is-not-relatively-embeddable`
  (`= D^+ = (A x Z) *_C A` non-hyperlinear, Gao Thm 7.1).  Under
  `sl3-z-weakly-ucp-stable` (confinement to the `Lambda`-exact face) this
  reduces, after `sl3-re-lambda-exact-coprime-face-is-unfaithful` (coprime
  levels) and `lambda-exact-face-of-the-collapse-closes` (regular-type
  2-power), to EXACTLY the `(RC3)` residual:
  `two-adic-tower-format-of-surviving-lambda-exact-enemy` — an
  `S_3`-interlocked depth-two solenoidal tower over `{SL_3(Z/2^a)}` with
  every marginal forced, being measured by the sioux tower probe (exact
  interlock floor `32/21` at `s = 1`).  The regular-trace-forces-regular-type
  shortcut is ruled out.  The other horn of the residual is the
  weak-ucp/outlier sector, i.e. flexible stability of `SL_3(Z)`
  (Dogon--Vigdorovich Q1.4 shape).
- *Atlas / binary Leavitt unit group (type ii, finite-combinatorial).*
  Reduces to finite certificates over `A8 = GL_4(F2)` and collision `19243`
  (`atlas-a4-holonomy-coherence-gap` family); several are being computed
  directly.
- *MIP*=RE transfer (type i).*  `non-ru-bcs-is-satisfiable-in-a-group-factor`
  (weakest form; any corner of any group factor modelling the fixed non-RU
  BCS), equivalent by `character-group-realizability-parseval-criterion` to
  a Parseval joint-state existence; blocked on embedding-universality of
  group factors (Chifan--Drimbe--Ioana Remark 1.1, open) or the
  Boolean-to-linear groupification (Paddock--Slofstra Prop 5.8, equivalent
  to the goal itself).

So every current route reaches the same class of frontier: a genuinely open
rigidity/stability question.  The RE pass's structural gain is that it
collapses the two by-hand routes onto one residual and states it as a
host-only, stable-letter-free question about microstates of `SL_3(Z[1/2])`.

**Capstone of the RE pass — the two ARITHMETIC routes collapse onto one
rank-one core.**  The Kostant computation
(`bounded-degree-two-primitives-for-higher-rank-lattices`, all `N >= 4`)
shows the operator-norm degree-2 primitive that the higher-rank
flexible-stability route needs is obstructed at the `(2,N-2)` Borel--Serre
cusp by a `GL_2`-block `SL_2(Z[1/p])`-Levi-fixed class, at EVERY rank.  So
raising the rank does not buy escape from rank one: the RCC/RE route
(through its weak-ucp/outlier horn) and the higher-rank flexible-stability
route both reduce to the SAME rank-one core,

```text
CORE A:  flexible HS-stability of the rank-one pair SL_2(Z) < SL_2(Z[1/2])
         (Dogon--Vigdorovich Question 1.4, the Iwahori / BS(1,4) lane).
```

The 2-adic tower residual is the `Lambda`-exact sub-case of CORE A; the
weak-ucp outlier residual is the non-exact sub-case; the cusp computation
shows both are rank-one at heart, so within the arithmetic family no route
escapes to a strictly easier object.  This does NOT reduce the WHOLE
program to CORE A: at least three further genuinely independent cores stand
outside the arithmetic family and are not touched by this pass ---

```text
CORE B:  a model of the fixed non-RU BCS in some group factor (MIP*=RE
         transfer; embedding-universality of group factors, CDI Rem. 1.1,
         or the Boolean-to-linear groupification, Paddock--Slofstra 5.8);
CORE C:  a non-residually-finite Kazhdan group, or Sp_4(Z), with LLP full
         C*-algebra (`non-hyperlinear-from-llp-non-rf-kazhdan`,
         `non-hyperlinear-from-sp2g-llp`; Fournier-Facio--Willett Q1.9/Q1.12);
CORE D:  the finite-combinatorial atlas certificates over A8 = GL_4(F2)
         (`atlas-a4-holonomy-coherence-gap`), self-contained and computational.
```

Net: the program is `CORE A or B or C or D` (plus the machine/reverse-Kleene
compilers, which feed CORE B via LCS perfect completeness).  This pass's
gain is specifically that the arithmetic RCC/RE and flexible-stability
routes are now proven to meet at CORE A --- one rank-one problem, not two
rank-dependent ones.

**Audit corrections to the frontier map and the four-core capstone
(2026-08-21, late).**  Three adversarial audits of the shortest paths
changed the following statements above.  (1) *Coprime face.*
`sl3-re-lambda-exact-coprime-face-is-unfaithful` is OPEN again: its step
`pi(h) in pi(Lambda)''` confuses the coordinatewise subgroup algebra with
the ultraproduct one (`congruence-slot-escapes-ultraproduct-lambda-algebra`);
the proved form needs the rate `eps_k log n_k -> 0`, so the `(RC3)`/RE
residual on the `Lambda`-exact face includes slow-rate coprime witnesses.
The sector collapse `odd-congruence-lambda-exact-sector-collapses` itself
stands.  (2) *Iwahori near sector.*  `iwahori-newton-closes-near-sector` is
OPEN again: the Newton step used a dimension-free second-derivative bound in
normalized HS, which does not exist
(`normalized-hs-taylor-remainder-is-not-dimension-free`); only an
operator-norm-proximity version holds.  The first-order theorem
`iwahori-uniform-infinitesimal-rigidity` stands, with its kernel statement's
"(T;FD)" justification unpacked (`SL_2(Z[1/2])` has (T;FD) though not (T);
CSP + Selberg give (T;FD), (T;FD) gives FAb, FAb gives `H^1 = 0`).  So
CORE A currently has NEITHER sector closed -- near (HS metric) nor far.
(3) *A fifth core.*  The type (i)/(ii) partition and the capstone
`CORE A or B or C or D` omit the Pestov lane: `hyperlinear-implies-sofic`
(Pestov Question 3.4, affirmative side) routes here by
`non-hyperlinear-from-hyperlinear-implies-sofic` through the nonsofic
Leavitt unit group, with twelve live holes across six sub-routes
(bounded-width compiler, cpsd face collapse, de Finetti rounding,
Markovization, traffic lifts, orbital rounding).  It is neither an
MIP*=RE transfer nor a by-hand non-CE factor, and it is independent of
A-D.  Likewise the Kun--Thom rigidity lane (`kt-centralizer-normalization-hs`
family), the Kervaire--Laudenbach lane, and the algebraic/Pontryagin
envelope lane (which reaches a group factor by duality and needs neither
embedding universality nor Paddock--Slofstra 5.8) are live and not
subsumed by the four named cores.  Honest count: the program is
`CORE A or B or C or D or E(Pestov)` plus three smaller independent lanes.
(4) *Tool note, withdrawn.*  An earlier draft of this note reported that
`bin/cairn frontier` listed `atlas-a4-rank-three-core-commutant-collapse`
as an open hole while `cairn why` called it refuted; on re-check the claim
was OPEN when that listing was taken and was refuted shortly afterwards by
`atlas-14-core-q19243-gl5-countermodel`, and the frontier view now agrees.
No tool defect.
