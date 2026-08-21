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

The self-referential gauge mechanism is also explicit.
`recursive-clifford-tail-supplies-anchor-but-not-contraction` realizes every
parent `CZ tensor V` with `V` equal to the product of its two child tail
gates; that child product is the exact same-gauge identity-outer anchor.
Finite-depth Clifford regular models prove the recursion is stationary, so
the remaining breakthrough must be a payload-dependent first-hit or
proper-corner exposure inequality with contraction factor below one.

Two analytic obligations have since closed. First,
`forbidden-weighted-type-carrier-coverage-is-rank-rounding` proves global
coverage with coefficient one and loss `3|Omega|/d`; hence the global
marked-type criterion now has only its summed-row domination gate. Second,
`tail-wordized-child-surplus-collision-supplies-rct7` converts forbidden BCS
surplus into the strict recursion

```text
(1+beta)a_n<=a_(n+1)+errors,
```

and one reflection-conjugacy word controls the only leakage term. Thus the
recursive lane's remaining obligation is finite-presentation wordization of
the tail and aggregate corrected child. A single ordinary Hecke holonomy
cannot provide the alternative global row domination:
`one-hecke-holonomy-cell-cannot-pay-the-cyclic-selector-sum` closes it by a
last-edge multiplicity-gauge countermodel.
