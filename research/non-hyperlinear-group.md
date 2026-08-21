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
