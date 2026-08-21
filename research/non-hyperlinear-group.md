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

The machine interface has now been reduced to a qualitative statement:
`threshold-free-reverse-kleene-higman-diagonal` needs only a compiler whose
NONHALT mark lies in the hyperlinear radical. The fixed-point program enumerates
a formal triviality proof and never reads a quantitative soundness modulus;
effective Higman embedding then promotes the resulting recursively presented
witness to a finitely presented one. The remaining mathematical work is wholly
in constructing that qualitative compiler. Two portfolio shortcuts have also
been closed cleanly: `sublinear-block-poisons-normalized-torsion` refutes the
unregularized determinant transfer, and
`twisted-group-basis-forces-affine-context-support` shows that native
projective-basis BCS observables already factor through affine/LCS contexts.

The adversarial-recursion ideas of the same date are integrated in
`research/artifacts/adversarial-error-delocalization-program-2026-08-21.md`.
Their surviving design is: use a separated mark to create positive-density
spectral mass, use recursion/expansion only to distribute consistency on that
carrier, allow an r.e. intrinsic challenge library, prove a standard-index
no-tail theorem in every matrix ultraproduct, and then apply threshold-free
Kleene plus Higman. Two exact firewalls prevent weaker versions:
`word-recursion-cannot-amplify-sublinear-summands` shows that direct-sum
naturality traps every finite recursive test inside a reducing `o(d)` corner,
and `universal-finite-packet-library-can-be-amenable` exhibits a two-generated
amenable group already containing every finite packet at its canonical
Plancherel fraction.
