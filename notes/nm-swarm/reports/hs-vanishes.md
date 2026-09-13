# Lane hs-vanishes: a producer of `HSVanishes` for the printed K

Target (ROSTER, census2 U5): a closed `NormalKazhdanPrintedRoute.manuscriptPrintedNormalKazhdan`
with no `HSVanishes` binder, or an in-repo producer of `HSVanishes` for the printed K.  Findings
to retire (`metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt`):

* line 79, `carrier-data GroupApproximation.Manuscript.OneSidedMFRadical.HSVanishes`
  (row `c36b6021a802`, tex 572, `cor:defect-hs`);
* line 66, `open-predicate GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptPrintedNormalKazhdan`.

## What was missing

`HSVanishes B g` (`PrintedForms.lean`) is the printed `‖V_n(g) − 1‖₂ → 0` for one operator norm
asymptotic representation `B = (V_n)`.  Corollary `cor:defect-hs` was proved only inside the named
proposition `PrintedDefectHS`.  The classifier does not unfold named propositions, so no corpus
declaration had conclusion head `HSVanishes`.  The hypothesis of `manuscriptPrintedNormalKazhdan`
("`HSVanishes` on every operator norm asymptotic representation") was therefore an open predicate.

## What this lane adds

Module `GroupApproximation/Manuscript/OneSidedMFRadical/HSVanishesProducers.lean`, namespace
`GroupApproximation.Manuscript.OneSidedMFRadical`:

* `hsVanishes_of_mem_opToHSShadowResidual`: `x ∈ R_{∞→2}(G)` gives `HSVanishes B x` for every `B`,
  since `R_{∞→2}(G) = ⋂_V K₂(V)`.
* `hsVanishes_of_mem_printedDefect`: if `L` has property (T) and `d ∈ 𝔇_G(L)`, then
  `HSVanishes B d`.  This is Corollary `cor:defect-hs` for one element, through the
  generator-by-generator inclusion `printedDefect_le_opToHSShadowResidual_direct`.
* Closed endpoint `PrintedCompressionCriterionHSHypothesis` /
  `manuscriptPrintedCompressionCriterionHSHypothesis`: the first sentence of the proof of
  `thm:compression-criterion` ("every operator norm asymptotic representation of `G` satisfies
  `‖V_n(k) − 1‖₂ → 0` for `k ∈ K ≤ 𝔇_G(L)`"), at the printed generality.
* Closed endpoint `PrintedCompressionCriterionCoronaTrivial` /
  `manuscriptPrintedCompressionCriterionCoronaTrivial`: the printed Theorem `thm:normal-kazhdan`
  (`manuscriptPrintedNormalKazhdan`) applied to the printed K.  Its Hilbert--Schmidt hypothesis is
  discharged by the first sentence, so every `k ∈ K` is corona MF invisible.

The lemmas carry `#audit_axioms` and the endpoints `#audit_closed_axioms`; all passed in the green
probe.  No literature input.

`manuscriptPrintedNormalKazhdan` keeps its `HSVanishes` hypothesis, because the printed theorem has
that hypothesis.  The lane meets the producer branch of the target.

## Why the two findings retire

In `scripts/check_non_mf_unconditional.py`, a carrier-data finding fires for a definition of a
proposition outside the `discharged_honestly` fixpoint.  An open-predicate finding fires for a
premise head that is not discharged.  `hsVanishes_of_mem_printedDefect` has conclusion head
`HSVanishes`, and its premises have heads `HasKazhdanPropertyT` and `OpAlmostRepresentation`, both
already produced.  So `HSVanishes` enters the fixpoint, and both findings stop firing.  I have not
run the classifier (no local compute).  The census lane's rerun removes baseline lines 66 and 79.

## Duplicate module, not to be wired

The same commit landed `GroupApproximation/Manuscript/NonMFSentences/IntroLimitingTraceSentence.lean`
(`PrintedIntroLimitingTraceIsTrivialCharacter`, `PrintedIntroSecondStepConclusion`), which is green
in the same probe.  Meanwhile sec2-sentences landed `LimitingTraceTrivialCharacterSentence`
(`0a8ef789f`) for the intro row `61827aea7807`.  That module's `PrintedLimitingTraceIsTrivialCharacter`
is stronger: it adds `Nonempty (KazhdanData K)` and `τ(π(e_K)) = 1`.  It also carries the footnote.
`PrintedIntroSecondStepConclusion` restates `manuscriptPrintedDefectNormalKazhdanRadical`.  So this
lane claims no row for tex 187 and does not queue `IntroLimitingTraceSentence` for wiring.  The lead
decided (2026-09-13) to leave it as an unwired orphan; no deletion lands.

## Conditional-baseline split (lead assignment, 2026-09-13)

The lead asked this lane to take the operator-algebra findings of the conditional baseline and to
agree the split with debt-conditional.  At origin/main `bb354f078` the baseline holds 102 findings.
Seven are operator-algebra:

| line | finding | owner | state |
| --- | --- | --- | --- |
| 66 | open-predicate `manuscriptPrintedNormalKazhdan` | hs-vanishes | retired by `850cd7b7d`; awaits the census rerun |
| 79 | carrier-data `HSVanishes` | hs-vanishes | retired by `850cd7b7d`; awaits the census rerun |
| 78 | carrier-data `IsStronglyOperatorMF` | baseline-debt (d) | producer landed unverified `95e6d09ca`; probe running |
| 97 | open-predicate `IsStronglyOperatorMF.isOperatorMF` | baseline-debt (d) | as line 78 |
| 171 | inlined-statement `manuscriptSentence_theoremQuotientTrivial` | baseline-debt (b) | in their probe |
| 238 | open-predicate `manuscriptSentence_cornerPassesUp` | baseline-debt (a) | `FullDefectPairLeavitt` landed unverified `95e6d09ca` |
| 298 | open-predicate `powersAveragingEstimate_of_naiveFreeProductProperty` | baseline-debt (c) | `NaiveFreeProductPropertyOfAcylindricallyHyperbolic` landed unverified `95e6d09ca` |

The other 95 findings have no operator-algebra input:

* debt-conditional's 59 buried-conditional and conditional-debt lines.  Its report (`7ab9c2f5f`)
  classifies them as 40 wall-only, 13 historical quasi-geodesic or unbounded Lemma 4.4, and 6 wall
  intermediates.
* The Theorem C and Hull endpoints and carriers over the four walls: carrier-debt 203 212 216 245
  249 252 283 296 297, carrier-data 267, and the 26 open-predicate lines from 214 to 307 other than
  238 and 298.

So this lane takes no further baseline line.  Messages went once each to debt-conditional and
baseline-debt, and the lead was asked for a wall piece.  The last census merge (export
`4626c73f2`) predates `2c3c8cb40`, which deleted the TheoremCAssembly sorries.  The conditional-debt
keys should therefore re-kind at the next rerun; this is a prediction, not a run.

## Rows (`metadata/nm-census-rows/hs-vanishes.tsv`)

| key | line | status | carriers added |
| --- | --- | --- | --- |
| `c36b6021a802` | 572 | formalized | `hsVanishes_of_mem_printedDefect`, `hsVanishes_of_mem_opToHSShadowResidual`; retires carrier-data `HSVanishes` and open-predicate `manuscriptPrintedNormalKazhdan` |
| `47c65457b63c` | 717 | formalized | `PrintedCompressionCriterionHSHypothesis`, `manuscriptPrintedCompressionCriterionHSHypothesis` |
| `4cd99c2ee1cb` | 717 | formalized | `PrintedCompressionCriterionCoronaTrivial`, `manuscriptPrintedCompressionCriterionCoronaTrivial` (first clause; the MF clause stays with the existing carriers) |

## Status

* LANDED `850cd7b7d`: both modules, landed unverified.
* Probe `0913-014626-72541` GREEN on base `a763cb445` (BUILT and COMPILED both modules).  The bytes
  on origin are identical, so the green landing reported NOTHING TO LAND (`49ad84503`).
* Rows LANDED `d785326e7`.
* Wire queue: `GroupApproximation.Manuscript.OneSidedMFRadical.HSVanishesProducers` at `850cd7b7d`;
  not yet root-wired at `bb354f078`.
* Residual propositions owned by this lane: none.  The target is met by the producer.  The retired
  findings await the census rerun.
* Next: no Lean in flight.  Waiting for the lead to name a wall piece and its integrator; the lane
  splits with the integrator before authoring.
