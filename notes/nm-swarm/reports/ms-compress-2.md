# Lane ms-compress-2: tex 468–582 (lem:kazhdan-projection-order, thm:transport)

Wave-2 range lane of session nonsofic-existence-49. The tex line numbers are at origin/main 68481e4d7. The census rows sit at
line numbers 458–567 of an older manuscript hash, so they were matched by label and text.

## Method

- Every row of `metadata/NON_MF_SENTENCE_CENSUS.tsv` with label `lem:kazhdan-projection-order` or `thm:transport` (28 rows)
  was read against the printed sentence.
- Every carrier statement was read on origin/main.
- Root closure: computed from the origin import graph (6530 modules). All 23 carrier modules are reachable.
- Conditional baseline: none of the 38 carrier declarations appears in `NON_MF_CENSUS_CONDITIONAL_BASELINE.txt`.
- Axiom audits: every endpoint carrier has `#audit_closed_axioms` or `#audit_axioms` on origin (1 to 3 lines each).

## Ledger

Verdicts: OK = closed, root-reachable, printed generality, printed route. GRADE = wrong carrier named. GAP = generality or
literal step missing.

| key | tex | status | verdict | carriers and note |
|---|---|---|---|---|
| 9bd4e2f1eaa1 | 470–471 | structural | OK | hypothesis frame; `LiteralMaximalCStarKazhdanProjectionOrder` binders |
| 1ff4a5b717b2 | 471–473 | definition | OK | `KazhdanData.projection`, unique extension `C*_max(L) → B` inside the endpoint |
| bad6f3c843a4 | 473–474 | formalized | OK | `manuscriptLiteralMaximalCStarKazhdanProjectionOrder`: any unital `B : Type v`, literal `≤` in the spectral order |
| bdceff578c1b | 479–481 | definition | GAP F2 | `manuscriptPrintedFaithfulNondegenerateRepresentation` binds `B : Type` and `[Nontrivial B]` |
| 7cf7dd61da4f | 481–482 | formalized | OK | `manuscriptSentence126_representedKazhdanProjection_range` (B, E in `Type (u+1)`: universe restriction only) |
| ea315c314c25 | 482–485 | formalized | OK | `KazhdanProjectionOneSidedOrder.symm_mem_of_conj_mem` at printed generality |
| ac2c96deddba | 485 | formalized | OK | clause 1 of `manuscriptSentence_movedFixedSpaceInclusionAndProjectionOrder` |
| e425c4fecaee | 486–487 | formalized | GAP F3 | carriers give the absorption form only; "`U*PU` is the orthogonal projection onto `U*Fix π(L)`" and the operator `≤` are not carried |
| 5292e3a80968 | 491–492 | structural | OK | `PrintedTransportHS` binders (`compressionSet L`) |
| 064a055d945c | 492 | structural | OK | `OpAlmostRepresentation` has no `V_n(1)=1` field, so the Lean theorem covers a larger class |
| 7229247f62b3 | 493–496 | formalized | OK | `TransportPrintedRoute.manuscriptPrintedTransportHS`, printed HS-bounded `𝒞₂` |
| 765fe31bdd7a | 502–507 | formalized | OK | `l2_opNorm_conjDouble_sub_le_two`, `opNorm_adConj_sub_le_two_mul` |
| a940b20e39ec | 507–514 | formalized | OK | `TransportSigmaTilde.tendsto_adMatrix_defect` |
| 6bf30ab286b0 | 515–516 | formalized | OK | `TransportSigmaTilde.sigmaTilde : G →* unitary 𝓑` |
| a6985193463f | 516–518 | formalized | OK | `card_adjoint_naturalizeCoordinates_model`, `manuscriptAdjointCoordinateSquareAndExactCoronaHom` |
| 87f873612529 | 518–521 | formalized | OK | `TransportProjectionCommutation.exists_projectionData` (lift by functional calculus) |
| 3df2cd0a86ce | 523–527 | formalized | OK | `manuscriptSentence_printedCTwoIffProjectionAbsorbs`, every lift `(P_n)` |
| e702793d4e6d | 528–533 | formalized | OK | `TransportKazhdanProjection.exists_combination_close` |
| ff42f7b64e53 | 534–536 | formalized | OK | same carrier: the `‖Σ a_ℓ − 1‖ < ε` clause |
| 36a9ae1219bf | 537–542 | formalized | OK | `TransportKazhdanProjection.limsup_norm_sub_combSeq_lt` |
| a5a02a73b909 | 543–550 | formalized | OK | `TransportProjectionCharacterization.tendsto_hsNorm_applyOp_projection_sub`; its proof carries the `2εc` estimate |
| 35313e7f2f61 | 551 | formalized | OK | same carrier |
| 734283523715 | 551–562 | formalized | OK | `tendsto_norm_adMatrix_mul_projection_sub`, `isHSAsymptoticallyCentral_of_tendsto` |
| 5c8aa0403a34 | 564 | definition | OK | `adjointCoronaHom` |
| fa1ec5f45603 | 564–568 | formalized | OK | `commute_sigmaB_projection`: absorption form of the lemma, then `manuscriptNormMatrixCoronaStableFinite` (printed route) |
| b2365e8ebb86 | 568–569 | formalized | GRADE F1 | names `manuscriptSentence_movedFixedSpaceInclusionAndProjectionOrder`, a Hilbert-space fixed-space lemma. The correct carriers are `commute_sigmaB_projection` and `TransportPrintedRoute.tendsto_norm_commutator` |
| 916db87815b7 | 569–578 | formalized | OK | `TransportPrintedRoute.tendsto_hsNorm_applyOp_projection_sub_of` |
| 6869e40b6f8c | 579–580 | formalized | OK | same carrier, applied to `Ad(V_n(u))^{±1}` in the endpoint |

## Findings

- **F1 (census grade):** row b2365e8ebb86 names a carrier that does not state the sentence. Fix: re-grade the row with
  `TransportProjectionCommutation.commute_sigmaB_projection` and `TransportPrintedRoute.tendsto_norm_commutator`. Both are
  root-reachable on origin.
- **F2 (generality):** "Fix a faithful nondegenerate representation of B on a Hilbert space" is for every unital
  C*-algebra B. The carrier covers only nontrivial `B : Type`. Fix: a carrier at every universe that also covers the
  trivial algebra.
- **F3 (literal step):** "Since U*PU is the orthogonal projection onto U*Fix π(L), it follows that U*PU ≤ P" has no
  carrier stating the projection's range or the operator order on the Hilbert space. Fix: a closed carrier with the range
  clause and `≤` in Mathlib's Loewner order on `E →L[ℂ] E`.

## Claims

- CLAIM F2, F3 carriers: `GroupApproximation/Manuscript/NonMFSentences/KazhdanProjectionOrderSentences.lean`
- CLAIM census re-grade of rows b2365e8ebb86, bdceff578c1b, e425c4fecaee: `metadata/nm-census-rows/ms-compress-2.tsv`
  (appended after the module lands)

## Audit coverage (requested by the lead after ms-intro-4's note)

- `Manuscript/OneSidedMFRadical/KazhdanTransportSentences.lean` (11 `manuscriptSentence_*` theorems) has no audit line in its
  source. On origin, 8 are audited in `Manuscript/NonMF/Audit/Intro.lean` or `Audit/Sec2.lean`. None audits
  `manuscriptSentence_residuallyFiniteKazhdanGroupsAreMF`, `manuscriptSentence_conjugationActionsMultiplicativeModC0` or
  `manuscriptSentence_restrictionExtendsToMaximalCStar`.
- `Manuscript/OneSidedMFRadical/RankTwelveConfiguration.lean` (29 theorems) has no audit line in its source. On origin, 8
  are audited elsewhere and 21 are not.
- CLAIM `GroupApproximation/Manuscript/NonMFSentences/TransportSentencesAxiomAudit.lean`: `#audit_axioms` for all 40
  theorems, plus `#audit_closed_axioms` for `printedDefectConfiguration` and `manuscriptPropositionDefect` (no binders).

## Item 2 (main ~18:40): help ms-inverses-4 on `OsinLemma94CaseOneTouchVertexStatement`

- Split sent directly to ms-inverses-4. ms-inverses-4 keeps its corrected `PocketWalkTouchOnlyShape` leaf, states the
  one-step interface (touch count strictly decreases on an O-equivalent labelled copy, values and side conditions kept), and
  runs the induction down to w1-binder-8's `false_of_simpleWalk_of_below`. This lane produces the step.
- Correction to the corner description in that message: the vertex split must cut at the two POCKET-side corners at the
  touch vertex, the faces `faceOf x_in` and `faceOf b_in`, so that `x_out` stays with `alpha x_in` and `b_out` with
  `alpha b_in`. The f-corner (`σ x_out = alpha x_in`) and the Π-corner are the corners kept. Those pocket-side faces can be
  relator cells or one face twice, so the thickening (edge doubling) goes on the pocket side.
- CLAIM pocket-side corner thickening at a touch vertex: `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketTouchCornerThickening.lean`
- ~~CLAIM the vertex split at a touch and the walk transport~~: dropped at ~19:00. The lead ruled the split, and
  ms-inverses-4 took it (its `Estimating/OsinPocketWalkSplit.lean`, `Estimating/OsinLemma94SameCellTouchSplit.lean`).
- Agreed ~19:00: this lane proves ms-inverses-4's `OsinPocketTouchCornerStatement` in `OsinPocketTouchCornerThickening.lean`
  (inputs 1–2 of the leaf). Both pocket corners are doubled with `FaceEdgeDoubling`, so each in-dart lies on a new G-digon.
  The corners are then distinct faces, not relator cells, and off the exterior, with no planarity lemma needed.
  - Delivered: an O-equivalent labelled copy and a dart map compatible with alpha, labels and vertices.
  - Also delivered: the exterior and the cell off the side of the transported walk, and the cell darts transported.
- Target text on origin: `OsinPocketTouchCornerStatement` (d1d4d90da, `Estimating/OsinPocketTouchSplitStatements.lean`). It adds the
  rotation clause: `σ′ (e d) = e (σ d)` unless `d = alpha in_k` or `σ d = in_k`.
- CLAIM side transport across the doubling: `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketTouchCornerSides.lean`
- CLAIM the closed proof of `OsinPocketTouchCornerStatement`: `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketTouchCornerProof.lean`
- CLAIM one doubling at a walk dart (rotation clause, exterior and cell off the side, carrier transport):
  `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketTouchCornerStep.lean`
- LANDED 9d4f00779 `OsinPocketTouchCornerThickening` (probe 0913-192658-884 GREEN): non-loop ⇒ face length ≥ 2, dart index,
  and the doubled dart on a G-cell digon off the exterior. Queued for wiring.
- LANDED a266c9a3d `OsinPocketTouchCornerSides` (probe 0913-193719-89977 GREEN): the dart projection of the doubled map,
  face-class chains projected, and faces off the side staying off it. Queued for wiring.
- LANDED f0e234f93 `OsinPocketTouchCornerStep` and `OsinPocketTouchCornerProof` (probe 0913-195503-80720 GREEN, both modules
  BUILT), queued for wiring.
  - `exists_doubling`: one doubling at a walk dart that is not a loop.
  - `osinPocketTouchCorner : OsinPocketTouchCornerStatement`, closed (`#audit_closed_axioms`): double along `in₁`, then
    along the image of `in₂`.
  - Two probe fixes before green: `EdgeInsertion.sigma_embed_apply` needs the `OsinPocketEdgeDoublingFirstTurns` import;
    its hypotheses are read at the insertion corners.
- Status ~20:15: the lead ruled that ms-intro-1's bbe90003a (`osinLemma94CaseOneXPocket_of_enclosed`, the X-pocket from the
  enclosed loop cut) makes the walk-level shape route unnecessary. Nothing new is started on it. Every claim of this item has
  landed, and the lane is free.

## Item 3 (main ~20:30): `OsinLemma94SameCellPocketInput` (hpocket of `_of_residualsV4CopySection`)

- Checked with w1-binder-2 in one message. It released its unwritten `Estimating/OsinUnboundSameCellPocketProof.lean`
  claim; nothing else of its touches the input. It keeps `BridgeComponentPlanar` (landed dc949da1e) and `BridgeComponentValue`
  (`listVal_pocket_eq_one`, the cell-free branch, re-probing).
- ms-traces-2 landed `EnclosedFaceSet` and `EnclosedSubdiagramLoopCutStatement` (a5dc9e6b0, e783c654c). The loop cut is
  stated, not proved.
- Route:
  - Cell-free branch: `BridgeComponent.listVal_pocket_eq_one`.
  - Relator branch (a relator cell other than cell `i` with a dart on the far side): the far-side faces enclosed by the
    pocket walk, then the enclosed loop cut with `s = []` and the pocket arc of cell `i`, then `OsinLoopCut.false_of_below`.
    The residuals get named statements.
- Model test first: a variant of ms-traces-2's `ClosedWalkIslandModel`, with exterior `[0]` and relator cells on `[4]` and
  `[1,2,5,3]`. The bridge has cell `i = [1,2,5,3]` on both sides.
  - At `d = 2`: every combinatorial clause holds, and the pocket `[5]` reads `gb⁻¹ ≠ 1`, so least area, the C-condition
    and the induction hypothesis carry the statement.
  - At `d = 3`: the orientation clause fails, and the pocket `[1]` reads `ga⁻¹ ≠ 1` with only the exterior on that side.
- CLAIM model test: `GroupApproximation/GGT/VanKampen/Estimating/OsinUnboundSameCellPocketModel.lean`
- CLAIM assembly of the pocket input over named residuals: `GroupApproximation/GGT/VanKampen/Estimating/OsinUnboundSameCellPocketAssembly.lean`
- Both paths are free on origin, in the shared tree and in every `lanes/*.files` (checked ~20:35).
- LANDED 96f7db6f6 `OsinUnboundSameCellPocketModel` (probe 0913-213347-38965 GREEN, BUILT), queued for wiring:
  `not_pocketValue`, `not_oriented_three`, `free_three`, `pocket_three_value`.
- 23:1x, after the coordinator restart: w1-binder-2's `BridgeComponentValue` is still not on origin.
  - Its re-probe 0913-203707-58823 failed; the `.green` record says PROBE FAILED.
  - The next re-probe hit the MSI outage, and w1-binder-2 has landed nothing since 20:42.
  - So the assembly takes the cell-free branch as the named statement `SameCellPocketCellFreeValueStatement`, which is
    `BridgeComponent.listVal_pocket_eq_one` verbatim, and imports origin modules only.
  - Once that module lands, discharging the statement takes one line.
- Assembly: `osinLemma94SameCellPocketInput_of_loopCut (hvalue) (hcut) : OsinLemma94SameCellPocketInput`.
  - The empty pocket is trivial.
  - Cell-free pocket: `hvalue`, with its side conditions from `OsinUnboundSameCellCycle.pow_inj`.
  - Far-side relator cell: `hcut` (`SameCellPocketLoopCutStatement`), then `OsinLoopCut.false_of_below` fed by the
    induction hypothesis, with `ρ` from `SameCellSimplePocket.exists_rho_large`.
- Probe fixes (bytes md5 8db1a498, attic copy pending):
  - 0913-232200-9064 FAILED: `have hrho : 0 < rho` shadowed the binder `hrho : max 1 rho1 ≤ rho`. Renamed to `hrho0`.
  - 0913-233848-93991 FAILED: `push_neg` is deprecated at the pin, and the warning is an error. Replaced by `push Not`.
  - The next two re-probes hit infrastructure: GitHub DNS failure, then the MSI connection down (rc=4, not Lean). A
    background loop waits for GitHub, saves the attic copy, and retries the probe until it stops failing on
    infrastructure.
- Routing from main (~00:0x 09-14):
  - `SameCellPocketCellFreeValueStatement`: w1-binder-5 takes over w1-binder-2's `BridgeComponentValue` and will send
    the names.
  - `SameCellPocketLoopCutStatement`: ms-traces-2 owns the successor-form enclosed route end to end. It has the exact
    statement text in one message, with an offer to respell before landing if its route needs more binders.
- ms-traces-2 confirmed no respell: its route has no collar at `g = []`, so it needs no label, `λ ≤ 1` or `0 ≤ c`
  hypothesis. The route:
  - carrier: `EnclosedFaceSetSucc` of the far faces;
  - `Ξ`: `BridgeComponent.component` through `DiscDiagram.ofPlanar`;
  - least area: `EnclosedPocketRegion.length_filter_le_of_bridgeFree` when bridge-free, otherwise its open
    `EnclosedBridgeDoublingSuccStatement`;
  - loop cut: `OsinLoopCut.ofTwoPartBoundary` at `g = []`;
  - still open: an enclosed analogue of `PocketCellTransportStatement`.
- LANDED bb887b17d `OsinUnboundSameCellPocketAssembly` (probe 0914-002811-94162 GREEN, BUILT), queued for wiring.
  - `osinLemma94SameCellPocketInput_of_loopCut (hvalue : SameCellPocketCellFreeValueStatement)
    (hcut : SameCellPocketLoopCutStatement) : OsinLemma94SameCellPocketInput`
  - The lane's in-flight file list is empty.
  - Remaining statements and their owners:
    - `SameCellPocketCellFreeValueStatement`: w1-binder-5, through `BridgeComponent.listVal_pocket_eq_one`
      (`BridgeComponentValue`, still not on origin). When it lands, one line discharges the statement, and this lane
      does that on receiving the names.
    - `SameCellPocketLoopCutStatement`: ms-traces-2's successor-form enclosed route, which targets the statement
      unchanged.

## Progress log

- 2026-09-13 ~17:05: ledger and claims.
- 2026-09-13 ~17:15: probe 0913-171415-11333 FAILED on `WithLp.ext_iff.mpr`, which is not usable at the pin since `p` is
  explicit. `manuscriptPrintedConjugatedProjectionOrder` elaborated with no error. Repaired through
  `(WithLp.equiv 2 (Fin 0 → ℂ)).injective.subsingleton`.
- 2026-09-13 ~17:30: resumed after the lead restart. Attic copies bef3710aa.
- 2026-09-13 ~17:35: probe 0913-173041-70991 GREEN (BUILT both modules). LANDED bb32c57f9:
  - `KazhdanProjectionOrderSentences`: `manuscriptPrintedFaithfulNondegenerateRepresentationEveryUnital` (F2) and
    `manuscriptPrintedConjugatedProjectionOrder` (F3), both `#audit_closed_axioms`.
  - `TransportSentencesAxiomAudit`: all 40 theorems of `KazhdanTransportSentences` and `RankTwelveConfiguration` pass
    `#audit_axioms`; `printedDefectConfiguration` and `manuscriptPropositionDefect` pass `#audit_closed_axioms`.
  - Both queued for wiring. Census rows bdceff578c1b and e425c4fecaee re-graded in `metadata/nm-census-rows/ms-compress-2.tsv`.
- Range status: all 28 rows of tex 468–582 are carried at printed generality along the printed route. F1–F3 are fixed.
  F2 and F3 become root-reachable once root-wire wires `KazhdanProjectionOrderSentences`.
