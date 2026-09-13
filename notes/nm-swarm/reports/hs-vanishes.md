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
| 66 | open-predicate `manuscriptPrintedNormalKazhdan` | hs-vanishes | producer `850cd7b7d`; removed as stale by the census merge `63f147d7b` |
| 79 | carrier-data `HSVanishes` | hs-vanishes | producer `850cd7b7d`; removed as stale by `63f147d7b` |
| 78 | carrier-data `IsStronglyOperatorMF` | baseline-debt (d) | removed as stale by `63f147d7b` |
| 97 | open-predicate `IsStronglyOperatorMF.isOperatorMF` | baseline-debt (d) | removed as stale by `63f147d7b` |
| 171 | inlined-statement `manuscriptSentence_theoremQuotientTrivial` | baseline-debt (b) | removed as stale by `63f147d7b` |
| 238 | open-predicate `manuscriptSentence_cornerPassesUp` | baseline-debt (a) | removed as stale by `63f147d7b` |
| 298 | open-predicate `powersAveragingEstimate_of_naiveFreeProductProperty` | baseline-debt (c) | removed as stale by `63f147d7b` |

At origin `304a14bad` each of the seven lines is a `# REMOVED by the census merge at 63f147d7b (stale:
matches no finding)` comment.  The baseline file there has 132 live lines and 63 removed ones, 51 of
them removed by `63f147d7b`.

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

## W1 h94 oriented metric layer (lead assignment, 2026-09-13)

The lead assigned this lane one piece of the metric half of Osin's Lemma 9.4 on wall hgreendlinger:
`OsinLemma94AntiparallelMetricStatement` (`OsinLemma94Pieces.lean`, `b8441172e`).  Its conclusion
is `∃ k, ∃ C : WordConnectorPair …, C.b' < C.b`.  The planar half refutes only that antiparallel
case (`OsinLemma94PlanarPolygons.no_antiparallel`), because Case 1 fills the quadrilateral
`X ++ target ++ Y ++ source⁻¹`.  hull-count94 owns the layer and did oriented Lemma 25 first
(`OlshanskiiFirstVisit`, `OlshanskiiOrientedLemma25`).
Its plan (`674b1b428`) names four more pieces:

1. `OrientedSidePair` / `OrientedClassPair`, with the restriction, rotation, inner-cut and outer-cut
   transports.  These only translate parameters, so they keep orientation.
2. The oriented three-class polygon lemma.
3. A monotone Morse index choice: on a `(λ, c)`-quasi-geodesic word, indices near geodesic
   parameters `t < t'` with `t' - t` above a constant satisfy `k < k'`.
4. `WordConnectorPair` with `target_backward : b' < b`, and the component-family theorem at that
   orientation.

The lead asked this lane to take a second piece, after confirming it with sec5-sentences rather than
hull-count94.  State at origin `304a14bad`:

* hull-count94:
  * `OlshanskiiFirstVisit` and `OlshanskiiOrientedLemma25` (`1c5f36398`), recorded GREEN in the wire
    queue.
  * `OlshanskiiOrientedClasses` (piece 1, `0963dc2b4`), recorded GREEN.
  * `OlshanskiiOrientedBisection` and `OlshanskiiOrientedThreeClasses` (piece 2,
    `orientedThreeClassPolygon`, `exists_orientedClassPair_of_aggregate_all`), landed `0ff430236`,
    recorded GREEN (03:10).
* sec5-sentences:
  * `UnboundMonotoneMorseIndex` (piece 3).
  * `UnboundOrientedWordConnectors` (`OrientedWordConnectorPair`, `OrientedWordSidePair`,
    `OsinUnboundScale.orientedWordSidePair_of_parameters`).
  * Both landed in `b1bd127ec`; the lane report records them in `4dc6bb7d4`.
  * `OsinUnboundScale.orientedWordSidePair_of_orientedClassPair` in `UnboundOrientedWordConnectors`,
    landed unverified `73caa3848`.  It takes an `OrientedClassPair` of the replacement polygon at
    segment length `(λ √ρ / 240 − c) / 1000` and closeness `12 (δ + 1)` and gives
    `OrientedWordSidePair`.
* In no lane file list:
  * The dense-component selection at side budget `∑ sideCount ≤ K n`.  `exists_component_gt_twoForty`
    is fixed to `53 n` arcs and `4` sides per arc.
  * The closed `OsinLemma94AntiparallelMetricStatement`, from `isHyperbolicSpace_cayley_of_fourPoint`
    and monotone thresholds as in `unboundWordPolygonMonotone`.

hs-vanishes proposed to sec5-sentences that it take both.  sec5-sentences answered that it had
already done both, after origin `7157facfd`, so this lane wrote no Lean for the layer:

* `779509227` (`UnboundOrientedWordPolygon`): `OsinUnboundScale.exists_orientedPolygonPair` and the
  closed `unboundOrientedWordPolygonMonotone : UnboundOrientedWordPolygonMonotoneStatement`.
* `e3da1ba60` (`OsinLemma94AntiparallelMetric`): `exists_component_dense_of_sideBudget` and the
  closed `osinLemma94AntiparallelMetric : OsinLemma94AntiparallelMetricStatement`, with
  `#audit_closed_axioms`.
* Probe `0913-034427-9910` GREEN (wire queue, 03:46).  Both modules are queued and not yet in the
  root.

So the metric half of Lemma 9.4 is closed.  The only open input of `osinLemma94Section_of_pieces`
is `OsinLemma94PlanarRunInput`, owned by hull-unbound.

Where the landed chain loses the orientation, which is where each piece plugs in:

* `exists_classPair_of_aggregate_all` returns `ClassPair`, and `SidePair` ends `β ≤ |t' - t|`.
  `OsinUnboundScale.exists_polygonPair` passes it on unchanged (pieces 1 and 2).
* `OsinUnboundScale.exists_originalArcPair_of_class_near` picks the Morse indices `a, a', b, b'`
  existentially from `hnear`, whose source is `exists_word_replacement_morse` (piece 3).
* `WordSidePair.exists_connectors` swaps `a ↔ a'` and `b ↔ b'` together when `a' < a`, and
  `unboundComponentWordPolygons` ends in `Nonempty (WordConnectorPair …)`, so `b' < b` is never
  recorded (piece 4).

Interfaces read at origin/main: `OlshanskiiPolygonClasses`, `OlshanskiiCutClasses`,
`OlshanskiiClassifiedBisection`, `OlshanskiiSmallClassBound`, `OlshanskiiThreeClasses`,
`OlshanskiiLemma25`, `OlshanskiiChord`, `UnboundPolygonCut`, `UnboundParameters`,
`UnboundPolygonGeometry`, `UnboundWordPolygon`, `UnboundWordPolygonMonotone`,
`UnboundComponentWordPolygons`, `UnboundWordConnectors`, `WordSegmentConnectors`,
`WordGeodesicReplacement`, `CayleyGeodesicMorse`, `OsinUnboundCaseOne`, `OsinLemma94Pieces`.

## W2 hbridge certificate cut (lead assignment, 2026-09-13)

The lead assigned this lane one piece of the Lemma 5.1 certificate cut on wall hbridge
(`HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement`).  hull-bridge, the integrator,
names the piece.  The route to the wall:

* `relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_letterPullback`
  (`GGT/HullSCLemma51EmbeddedProducer`) reduces the wall to `QuotientPeripheralLetterPullbackStatement`.
* `quotientPeripheralLetterPullbackAt_of_letterStepBound` (hull-component,
  `GGT/HullSCLemma51LetterPullbackInduction`) reduces that to two `LetterStepBound` moves:
  * M1, a non-geodesic rotation: `letterStepBound_of_not_isRelGeodesic`, on main;
  * M2, the certificate cut.

State of M2 at origin (04:18):

* CutFaces and CutSides `14850636f` (hull-component): `CutFace`, the side and arc value lemmas,
  `CutFace.left_designated`, `CutFace.right_designated`.
* CutBlocks `4d91f2870`: the quotient blocks, `RotatedLift.arc_left`, `arc_mid`, `tail_left`,
  `tail_mid`.
* CutLift `dfa2dfb11` (hull-bridge): `CutLift`, the proposition `CutLiftOutcome W D q hq`,
  `CutLift.null_word`, `CutLift.length_lt`, `pullbackOutcome_of_blocks`.
* CutOutcome `a1f2e52da` (hull-component): `CutMove`, with
  * `CutMove.outcome_before`: the arc lies before the unknown letter;
  * `CutMove.mem_image_of_inner`: the arc runs through the unknown letter, and no side letter reads
    at its coset.

Open, as read from origin:

1. The designated case.  The arc runs through the unknown letter `comp λ h⁻¹`, and a letter of `L`
   or `R` reads at its coset.  Its respelled inverse has value `X · h⁻¹ · Y` (`left_designated`,
   `right_designated`) and becomes the designated letter.
2. The proof of `CutLiftOutcome`, or its `CutMove` form.
3. Cut: `LetterStepBound D W q hq (fun w => ∀ r, IsRelGeodesic D (w.rotate r))` under `hsc`, `hmu`,
   `hrho`, `hker`, `hcert`.  It comes from `exists_geodesicCut_of_leastAreaCertificates`,
   `exists_rotatedLift` and item 2.
4. Holds: `QuotientPeripheralLetterPullbackStatement`, from `(M1).or (M2)` and
   `quotientPeripheralLetterPullbackAt_of_letterStepBound`.

The lead reports that debt-conditional and leavitt-units each hold one of CutOutcome, Cut and Holds.
`CutMove` (hull-component) and `CutLift` (hull-bridge) carry nearly the same data.  hs-vanishes asked
hull-bridge once for one unstarted piece.  hull-bridge answered that none is left:

* Item 1 is hull-component's.  `outcome_left` is on main at `27f56e14b`, and `outcome_right` is in
  the unlanded `GGT/HullSCLemma51LetterPullbackCutOutcomeRight`.
* Items 2 and 4 are hull-bridge's `GGT/HullSCLemma51LetterPullbackHolds`, already written.
  `CutLift.toCutMove` turns each `CutLift` into a `CutMove`, and the proof splits into four cases.
* Item 3 is debt-conditional's, green at `457c543a8`.

The pieces are stated on `CutMove`.  So this lane wrote no Lean on W2.

## W1 C5 of `PhiPrimeCountInput` (lead assignment, 2026-09-13)

`PhiPrimeCountInput` (`GGT/VanKampen/Estimating/OsinAppendixEulerCount.lean:52`, owned by hull-euler) is
the Euler count `|M| ≤ 3(n + r − 1)` of Osin's `Φ'_M` (Appendix, Lemma 9.3).  hull-euler's plan (report
`fbef94518`) proves it with one merged outer vertex `O`, in steps C1 to C6.  The lead gave this lane
C5:

* C5 injects every two-gon that C4 does not cover, and whose face class holds a cell, into the
  components not linked to `O` and the isolated cells.
* It uses (J) `CombMap.IsRestriction.faceOf_eq_of_faceClass` (`CombMapRestrictionFaceClasses`,
  `9fdb80035`, probe `0913-032836-75226` green).  It sums over the components with
  `card_le_of_linked` (`OsinAppendixEulerPhiBound`).

hull-euler states C5 as a named proposition and sends this lane its Lean name and file.  This lane
writes no Lean until then.  After that it proves C5 in a new module of its own: statement landed
unverified, then proof, probe and landing.

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
* Rows LANDED `d785326e7`.  Report LANDED `031bcc87b`, updated in `3e34da4ea`, `a4c5b47db`,
  `840e6a1d8`, `395b3c31c` and by the commit that carries this section.
* Wire queue: `GroupApproximation.Manuscript.OneSidedMFRadical.HSVanishesProducers` at `850cd7b7d`;
  root-imported by root-wire's wave 2, `c72bdfd5d` (02:45).
* Census merge `63f147d7b` (files at `94bb0a9f8`, 02:41): baseline lines 66 and 79 removed as stale.
  The three rows merged as `partial`.  The merge predates the root import, and a formalized row now
  needs its carriers in the root closure; the next merge regrades them.
* Residual propositions owned by this lane: none.  The target is met by the producer.
* W1 h94: no piece for this lane.  The metric layer closed through sec5-sentences (`e3da1ba60`).
* W2 hbridge: no piece for this lane.  hull-bridge has none left.
* Next: C5 of `PhiPrimeCountInput`, once hull-euler names the proposition and its file.  No Lean in
  flight.
