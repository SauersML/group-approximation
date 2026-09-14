# Lane ms-intro-1: tex 1–165 (abstract, Introduction opening)

Lead: session nonsofic-existence-49, wave 2 (range audit and fix). Manuscript at origin/main 68481e4d7; tex 1–165 is
unchanged since the census extraction, so census line numbers match here.

## CLAIM

- CLAIM carrier of tex 162–164 (general clause "c ∈ C_G(L) ⇒ ucu⁻¹ commutes with uLu⁻¹", plus "need not commute with
  the rest of L") — `GroupApproximation/Manuscript/NonMFSentences/IntroCompressorCentralizerSentence.lean`
- CLAIM Korchagin sentence (tex 99–102) at the literal printed definition — `GroupApproximation/Manuscript/NonMFSentences/KorchaginLiteralSentence.lean`
- CLAIM (17:20, raised by ms-core-1 through main) closed bridge between the corona form `IsOperatorMF`, which
  `isOperatorMF_of_isLEF` and others produce, and the printed MF definition of tex 87–98 —
  `GroupApproximation/Manuscript/NonMFSentences/IntroMFDefinitionCoronaBridge.lean`. On main before this lane:
  `PrintedMFDefinitionLiteral` (IsCDEOperatorMF ⟺ printed models), `PrintedMFUnitaryModels` (IsCDEOperatorMF ⟺
  pairwise-uniform models, no V_n(1)=1) and the lemma `isCDEOperatorMF_iff_isOperatorMF` (`#audit_axioms` only). No closed
  Prop states IsOperatorMF ⟺ the printed definition.

Both paths are free on disk, on origin and in every `lanes/*.files`; the planned names have no hit on origin or in the
shared tree (checked 2026-09-13 ~17:05).

## Ledger (31 census rows, every sentence of tex 59–165 has a row)

Verdict `OK` means: carriers exist on origin/main, are root-reachable (through `Manuscript/NonMF/Audit/Intro.lean`,
root-imported at `GroupApproximation.lean:4868`, or directly), the endpoint has `#audit_closed_axioms`, and the
statement matches the printed sentence at the printed generality.

| key | tex | status | verdict |
|---|---|---|---|
| 7b8f14aa4de8 | 59 | structural | OK (`\frenchspacing`) |
| 3393c0cf411c | 68 | formalized | OK: `manuscriptNotEveryCountableGroupIsMF` |
| 113e60b5f202 | 69 | formalized | OK: `manuscriptOneSidedCompressionCriterion` (normal (T) K ≤ printedDefect L ⇒ K ≤ Rad_MF) |
| e82d3011b6cb | 72 | formalized | DEFECT, fixed in rows: named only `manuscriptNotEveryCountableGroupIsMF`, which carries none of FG, simple, (T), trivial MF homs, C*_r separable, stably finite, not MF. Carrier is `UnitGroupHeadline.manuscriptUnitGroupHeadline` |
| a16637da7249 | 76 | partial | W1 (torsion-free clause, hgreendlinger); owner: the other swarm |
| cff73e6439ba | 83 | structural | OK |
| 88e8012cb87e | 87 | formalized | OK: `manuscriptIntroductionMFDefinition` (literal V_n(1)=1, multiplicativity, limsup separation ⟺ IsCDEOperatorMF) |
| 6201111b83a0 | 94 | definition | OK: `manuscriptNormalizedMFModelSeparation` |
| b1b04e376fe7 | 99 | formalized | DEFECT, fixed in rows: named the strong-convergence carriers of the next sentence. Carrier is `KorchaginSentence.manuscriptSentence_korchaginFullSequenceSeparation` (IsOperatorMF ⟺ WeakMFApproximation). Literal-shape upgrade CLAIMED above |
| 837b7cffa562 | 102 | formalized | OK: `IsStronglyOperatorMF`, `not_isStronglyOperatorMF_of_not_isOperatorMF` |
| 8d0b87a46a51 | 106 | definition | DEFECT, fixed in rows: "Equivalently, G embeds in U(Q_d)" asserts an equivalence; regraded `formalized` with `manuscriptIntroductionMFDefinition` + `isCDEOperatorMF_iff_isOperatorMF` (arbitrary positive d_n) |
| be1769283b2f | 112 | definition | OK: `PrintedBoundedProductsNullIdeal` |
| d31180a98ce2 | 114 | definition | OK: `CoronaHomomorphism` |
| ad33e493e32f | 116 | formalized | OK: `IsMFAlgebra A ↔ Separable ∧ HasMFEmbedding A` |
| 3f00927a7193 | 117 | structural | OK ("Write") |
| 10e027681ba5 | 122 | definition | OK: `manuscriptSentence_mfRadicalFormula` |
| f2a05ccf5990 | 122 | formalized | OK: `PrintedMFRadicalQuotientIsMFAndLargest` (kernel = Rad_MF, surjective, quotient MF, unique factorization) |
| 5c93c70edc4c | 126 | formalized | OK |
| 5a7e84235409 | 126 | structural | Preview sentence. Its plural "groups" includes the torsion-free Q (W1-partial). Kept structural: the previewed theorems carry their own rows (thm:headline, thm:amenable-trace, thm:torsion-free) |
| 0f8b4d96c68f | 130 | structural | OK |
| 651e122a919e | 134 | definition | OK: `PrintedCliffordWitnessGroup` (audit-intro, 798be51a3) |
| 9930600167a4 | 140 | formalized | OK: `manuscriptSentence_witnessMFHomKillsSign`, root-imported (`GroupApproximation.lean:4938`); the footnote is provenance inside the same sentence |
| 23e47f0da468 | 144 | structural | OK |
| 8766dc520cfb | 146 | formalized | OK: `PrintedIntroUnitGroup` carries simple, trivial MF homs, R_R ≅ R_R ⊕ R_R, H ≅ Aut(R_R), H ≅ GL_n(R), GL_n = EL_n for all n ≥ 2, all proved (Khanh–Thanh is attribution) |
| 374637bc6ac7 | 153 | attribution | OK |
| ec81a8c16b64 | 156 | definition | OK: `PrintedCommutatorConvention` |
| f355d5f61dd8 | 157 | formalized | OK: compression criterion |
| effc40395f2b | 160 | definition | OK: `compressionSet`, `mem_compressionSet_iff` |
| b671ae1aab2b | 162 | formalized | GAP: the general clause "so ucu⁻¹ commutes with uLu⁻¹" is carried only by rank-twelve instances. Carrier CLAIMED above |
| 56d73653208a | 164 | definition | OK: `printedDefect` (the display at 166+ belongs to ms-intro-2) |

## Literature inputs in range

- `\cite{CDE}` (MF definition): definition, literal (`IsCDEOperatorMF`).
- `\cite[Props 2, 7]{Korchagin}`: proved (`exists_weakMFApproximation` plus the local-model converse); no binder.
- `\cite{GaoEtAl,Schafhauser}`: definition of the convention plus a proved contrapositive.
- `\cite{BK}`: definition.
- `\cite{KhanhThanh}`: attribution; every clause proved (`PrintedIntroUnitGroup`).
- `\cite{OAI}`: attribution.

## Progress log

- 17:05 ledger landed with census row corrections for e82d3011b6cb, b1b04e376fe7, 8d0b87a46a51
  (`metadata/nm-census-rows/ms-intro-1.tsv`), db35aee00.
- 17:15 LANDED c28a60924 (probe 0913-170314-63885 GREEN, both modules BUILT):
  - `Manuscript/NonMFSentences/KorchaginLiteralSentence.lean`: `PrintedKorchaginLiteral`,
    `manuscriptSentence_korchaginLiteral`. This is tex 99–102 between the printed model conditions: limsup separation ⟺
    one constant along the full sequence, with V_n(1)=1 kept on both sides. Row b1b04e376fe7 now names it.
  - `Manuscript/NonMFSentences/IntroCompressorCentralizerSentence.lean`: `PrintedCentralizerConjugateCommutes`
    (general), `PrintedConjugateNeedNotCommute` (rank-twelve witness, defect ≠ 1),
    `manuscriptSentence_compressorCentralizer`. Row b671ae1aab2b now names them.
  - Both modules are queued for wiring in `wire-queue.txt`.

- 17:20 LANDED 0f5189f9a (probe 0913-171351-8828 GREEN, BUILT): `Manuscript/NonMFSentences/IntroMFDefinitionCoronaBridge.lean`,
  `PrintedMFDefinitionCoronaForm` and `manuscriptSentence_mfDefinitionCoronaForm`. For every countable G, IsOperatorMF G ⟺
  the printed definition of tex 87–98. Corona-form producers such as `isOperatorMF_of_isLEF` (tex "countable LEF groups
  are MF", raised by ms-core-1) now reach the printed notion by `.mp`. Rows 88e8012cb87e and 8d0b87a46a51 name it; the
  module is queued for wiring.

## W1 binder 3 help (main, ~17:40): OsinLemma94CaseOneSameCellStatement

- Proposed to w1-binder-3: A = the pinch split of the pocket walk, B = the empty windows. Its turn ended with no overlap
  and a tip: `not_mem_sideFaces_or_of_barrier_noncrossing` (e3843182e) serves lobes.
- CLAIM value split of a closed dart walk at a repeated vertex (lobes are closed, their values multiply along the rotation,
  so a walk reading ≠ 1 has a lobe reading ≠ 1) — `GroupApproximation/GGT/VanKampen/ClosedWalkPinchSplit.lean`.
  Path and names are free on origin, in the shared tree and in every `lanes/*.files` (checked ~17:45).

### Finding: pinched lobes break hnorm (route check before building)

Route of the relator-cell branch (`OsinLemma94CaseOneRCellStatement`, jacobson in flight, and
`false_of_pocketRegion_of_below`):
- Under R1 the loop cut needs `hin` and `hout`. `PocketRegion.isSimpleClosedWalk_invDarts_outer`
  (OsinPocketRegionVertexSimple:268) makes the pocket walk simple, so the loop cut takes only simple pocket walks.
- `nonempty_osinLoopCut_of_pocketRegion` (OsinPocketLoopCut:201) also needs `invDarts P.outer.cycle = s ++ invDarts A.darts`
  with `‖val s‖ ≤ ε`.
- Case 1 X-pocket walk `invDarts X ++ invDarts B`, where X runs along the polygon face from a' to b' and B along ∂Π from b'
  to a'. Pendant removal takes out spurs but not pinches, and three pinch shapes arise:
  1. v twice on X (the face pinches, a bubble of f): excise the lobe L. If L reads 1, the X-part keeps its value, so the
     norm stays < ε, but the face-walk rotation hypothesis is lost. If L reads ≠ 1 it is a bubble with relator cells.
  2. v twice on B (∂Π pinches): the analogous bubble of Π.
  3. v on X and on B (f touches Π at a vertex; this is not a side, since sides are made of darts): the lobes are
     `X₁ B₂` and `X₂ B₁` with `X = X₁ X₂`. Each lobe's side is a sub-segment `X₁` or `X₂` of X. Only ‖val X‖ < ε is
     controlled (`wordNorm_lt_of_end_connector`), because X runs along other polygon sides between a' and b'. So neither
     lobe meets hnorm, and route A cannot feed the loop cut on shape 3.
- Empty windows (B): `X = []` with `B ≠ []` makes B a closed arc of ∂Π reading ≠ 1, which is shape 2 again, so B is not
  a separate cheap leaf.
- Consequence for the producer: the relator-cell branch needs a named statement for shapes 1–3, or an argument that least
  area, DartMinimal or Maximal excludes shape 3. Nothing on origin states either. sec5-sentences' hair-opening and
  bubble un-pinch Props are not on origin (only `SurgeryHairOpening.IsHair`).

### Landed: the pinch split

- LANDED 8b0c76b7d (probe 0913-180113-80260 GREEN, BUILT): `GGT/VanKampen/ClosedWalkPinchSplit.lean`, queued for wiring.
  - `IsClosedDartWalk` and `IsSimpleClosedWalk.isClosedDartWalk`.
  - `IsClosedDartWalk.take` and `.drop`: the two lobes at a repeat of the first vertex at position `k`.
  - `listVal_dartWord_eq_mul_lobes`, `exists_lobe_listVal_ne_one`, `pinchSplit`.

### Ruling (main ~18:00) and model verdict for shape 3

- Ruling: land the split; model-test whether least area, DartMinimal or Maximal excludes shape 3; state shape 3 as a named
  Prop in this lane's module; land the reduction of the X-pocket case plus the shape 1–2 excisions.
- Verdict of the definition check at origin 8b0c76b7d: none of the three conditions constrains a vertex touch.
  - `DiscDiagram.LeastArea` (OsinAppendixSections:114) counts relator cells.
  - `DartMinimal` (OsinLemma94PlanarPieces:148) minimizes `dartCount` at equal `unboundSum`. A touch uses no dart, and
    separating f from Π at v (a vertex split) adds darts, so DartMinimal favours the touch, if anything.
  - `Maximal` (OsinLemma94PlanarPieces:205) constrains the junction of consecutive sides of one kind. A touch is not a
    side, since sides are dart lists.
  - So no exclusion argument follows from the definitions, and a route that needs hnorm on a lobe has no support.
- A full labelled model is not built. It would need a concrete C(ε, μ, λ, c, ρ) instance (hyperbolic group, long
  quasi-geodesic relators), a `GloballyDistinguishedSectionFamily` whose `weight_maximal` and `card_minimal` range over
  every realized family, DartMinimal over every family, and polygons. No lane has built such a model; the existing
  labelled models (OsinPocketLakeLabelledModel, OsinPocketMultipleEdgeLakeModel) stop before least area and the family.
- CLAIM shape Props for the Case 1 X-pocket (simple, face bubble, cell pinch, vertex touch, spur) and their case
  reduction — `GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94SameCellPocketPinch.lean`. It consumes only origin
  names: the binder block of `OsinLemma94CaseOneSameCellStatement`, `osinLemma94CaseOneWalk_sameCell`, `sideFaces`.

### Subsumption note (found ~18:15, after 8b0c76b7d landed)

- `ClosedWalkFaceColouring` (kh-ejz, on main) already has `ClosedChain`, `closedChain_iff`, `closedChain_append_comm`
  (rotation) and `closedChain_split`, a pinch split at the chain level. So the combinatorial half of
  `IsClosedDartWalk.take` and `.drop` is subsumed there; my grep for split lemmas missed it because it used different
  names (`closedChain`, not `split_at_vertex` or `pinch`).
- New in ClosedWalkPinchSplit: the values (`listVal_dartWord_eq_mul_lobes`, `exists_lobe_listVal_ne_one`,
  `listVal_dartWord_drop_eq_of_take_eq_one`) and the take/drop form.
- In flight: `isClosedDartWalk_iff_closedChain` credits and bridges to the chain-level lemmas. To excise a lobe that
  reads 1 in the middle of a walk, rotate it to the front with `closedChain_append_comm`, then apply the front
  excision.

### X-pocket shape statements (in flight, `Estimating/OsinLemma94SameCellPocketPinch.lean`)

- `OsinLemma94CaseOneXPocketStatementOf shape` takes:
  - the binder block of `OsinLemma94CaseOneSameCellStatement`, the output of `osinLemma94CaseOneWalk_sameCell` and the
    carrier rotation `q B p A`;
  - `X B` reading ≠ 1 and the exterior face off `sideFaces (invDarts X ++ invDarts B)`;
  - the condition `shape` on `(invDarts X, invDarts B)`.
  It concludes False.
- Shapes: `PocketWalkSimpleShape` (the loop-cut case, jacobson), `PocketWalkFaceBubbleShape` (shape 1),
  `PocketWalkCellPinchShape` (shape 2), `PocketWalkTouchVertexShape` (shape 3), `PocketWalkSpurShape`.
- Named statements: `OsinLemma94CaseOneSimplePocketStatement`, `...FaceBubbleStatement`, `...CellPinchStatement`,
  `...TouchVertexStatement`, `...SpurStatement`, and `OsinLemma94CaseOneXPocketStatement` (no shape).
- `osinLemma94CaseOneXPocket_of_shapes` proves the X-pocket statement from the five. When there is no spur, no touch and
  no repeated vertex on either part, the whole walk repeats no vertex (`List.nodup_append`).
- First probe 0913-181127-19691 FAILED: the FaceBubble and CellPinch predicates picked up only one of the section
  variables `x b`. Fixed with explicit binders.
- LANDED f82985905 (co-probe 0913-181424-38318 GREEN, both modules BUILT):
  - `Estimating/OsinLemma94SameCellPocketPinch.lean`: the five shape statements and `osinLemma94CaseOneXPocket_of_shapes`.
  - `ClosedWalkPinchSplit.lean` update: `isClosedDartWalk_iff_closedChain` and
    `listVal_dartWord_drop_eq_of_take_eq_one`.
  - Both modules queued in `wire-queue.txt`.
- Residual statements this module leaves open, with owners still to be ruled by the -ce lead:
  - `OsinLemma94CaseOneSimplePocketStatement` (the loop-cut case; jacobson's route through `false_of_pocketRegion_of_below`
    plus w1-binder-3's `hi` and side selection);
  - `OsinLemma94CaseOneFaceBubbleStatement` (shape 1);
  - `OsinLemma94CaseOneCellPinchStatement` (shape 2);
  - `OsinLemma94CaseOneTouchVertexStatement` (shape 3, no exclusion from the definitions);
  - `OsinLemma94CaseOneSpurStatement` (pendant removal, 61c2ade8e, is the candidate producer).
  The Y-pocket twin is not stated; it is the same statement with `Y A`.

### Assignment (main ~18:30): Spur and FaceBubble; BLOCKER finding

- Assigned: `OsinLemma94CaseOneSpurStatement` via pendant removal and `OsinLemma94CaseOneFaceBubbleStatement` via front
  excision. The other shapes went to w1-binder-8 (Simple), ms-inverses-1 (CellPinch), ms-inverses-4 (TouchVertex) and
  ms-intro-3 (Y-pocket twin).
- Sent w1-binder-8 the Simple interface, with a request to export the kill at walk level: a simple walk
  `s ++ invDarts T.darts` with ‖val s‖ ≤ ε.
- Finding (from `OsinLemma94RealizedPolygons`, OsinLemma94PlanarPieces:62):
  - `face k` is an unselected G-face.
  - A `.cutting` side has `faceOf (alpha d) = face k` for all its darts (`cutting_internal`), i.e. a bridge of f.
  - Each cutting path appears twice on the polygon walk, and X can hold both copies: `X = X₁ t X₂ t⁻¹ X₃`, around an
    island that f surrounds. That configuration is both the Spur shape (d and alpha d in x) and the FaceBubble shape
    (the attachment vertex repeats).
  - Pendant removal only kills pendant paths, which DartMinimal already excludes. So "Spur via pendant removal" covers
    almost nothing.
- Reachable: a lobe `t X₂ t⁻¹` reading 1 can be excised with the value and the norm of the side kept. That needs the
  walk-level kill.
- Not reachable on origin: an island with a relator cell.
  - The lobe's boundary lies on f, has uncontrolled norm, and has no cell arc.
  - The pocket side is disconnected, so it is not a PocketRegion.
  - The loop cut (R1) takes PocketRegions only. Osin's Γ contains the islands.
- Reported to main as a blocker. Options put to main: (a) a loop cut from the enclosed singular subdiagram of a walk;
  (b) a named island statement; (c) restate the branch at component level.
- CLAIM (route-independent, while the ruling is pending) spur lobes and their conjugate values —
  `GroupApproximation/GGT/VanKampen/ClosedWalkSpurLobe.lean`.

### Ruling (main ~18:50): island statement now, design of (a) after, not (c)

- LANDED a2b068902 (probe 0913-191029-41233 GREEN; the lobe module was built in 0913-190306-208):
  - `ClosedWalkLobeExcision.lean`: `IsClosedDartWalk.append_comm`, `rotate_at`, `lobe`, `excise`,
    `listVal_dartWord_eq_mul_lobe`, `listVal_dartWord_excise_of_lobe_eq_one`.
  - `Estimating/OsinLemma94SameCellPocketIsland.lean`, the walk-level X-pocket. The walk is `s ++ invDarts B`, with
    `s <+ invDarts X` and `val s = val (invDarts X)`, closed, and the exterior face off its side. It states
    `OsinLemma94CaseOneWalkSimpleStatement`, `OsinLemma94CaseOneIslandStatement` (a lobe of s reading ≠ 1),
    `OsinLemma94CaseOneExcisionStatement` (a lobe of s reading 1), `...WalkCellPinchStatement` and
    `...WalkTouchVertexStatement`, and proves `osinLemma94CaseOneXWalk_of_shapes` and
    `osinLemma94CaseOneXPocket_of_walkShapes`.
  - Exhaustiveness: when no touch, no repeat on b and no repeat on s, the walk repeats no vertex. A dart with its reverse
    on such a walk forces `[d, alpha d]`, which reads 1 (`IsClosedDartWalk.listVal_eq_one_of_alpha_mem`), against `X B`
    reading ≠ 1. So spurs and face bubbles need no statement.
  - The bridge to fixed X uses w1-binder-8's `SameCellPocketWalk.isClosedDartWalk_X`.
- INCIDENT (~18:40): I wrote this module over w1-binder-8's landed path `Estimating/OsinLemma94SameCellPocketWalk.lean`
  in the shared tree, without the path check. Origin was unaffected. Restored at ~18:58 to origin blob fdc1bb2b (equal to
  its `.v2` backup), the path was removed from my `.files`, and w1-binder-8 was told. Attic copy ec4bf8227 is text only.
- Residuals I own: `OsinLemma94CaseOneExcisionStatement`.
- LANDED 32910e583 (probe 0913-193156-69932 GREEN, BUILT): `Estimating/OsinLemma94SameCellWalkSimple.lean`,
  `osinLemma94CaseOneWalkSimple : OsinLemma94CaseOneWalkSimpleStatement`, CLOSED via w1-binder-8's
  `SameCellSimplePocket.false_of_simpleWalk_of_below`. The sub-walk side lemma is
  `SameCellWalkSimple.face_not_mem_sideFaces_sublist`. Queued for wiring.
- DESIGN (~19:45, after reading ms-traces-2's unlanded `ClosedWalkEnclosedSubdiagram` and
  `OsinEnclosedSubdiagramLoopCut`): Island and Excision share ONE consumer, applied to the whole pocket walk. No excision
  is needed.
  - `EnclosedSubdiagramLoopCutStatement` takes `EnclosedFaceSet X faces outerWalk` with `invDarts X outerWalk = s ++
    invDarts X A.darts`. Take `outerWalk := invDarts (s ++ invDarts B) = B ++ invDarts s`, `A.darts = B`, `faces :=
    sideFaces (s ++ invDarts B)`. This works for any shape, and bridges (cutting paths) are allowed.
  - The consumer module (mine, after their statement modules land):
    - (i) the producer `EnclosedFaceSet X (sideFaces w) (invDarts w)` for the Case 1 X-walk w, with the exterior face off
      its side;
    - (ii) `(cell j).face ∉ sideFaces w` for walks with spurs, where the landed sublist lemma needs noncrossing;
    - (iii) a cell-free enclosed face set reads 1, giving a relator cell inside from `val w ≠ 1` (the singular form of
      `PocketRegion.listVal_outer_eq_one`; w1-binder-2's BridgeComponentValue is the component form);
    - then `OsinLoopCut.false_of_below`.
  - So no `sideFaces` monotonicity Prop is needed for Excision.
- LANDED bbe90003a (probe 0913-194940-66027 GREEN, BUILT): `Estimating/OsinLemma94SameCellPocketEnclosed.lean`,
  `osinLemma94CaseOneXPocket_of_enclosed (hloop : EnclosedSubdiagramLoopCutStatement) (hface :
  EnclosedFaceSetOfNoncrossingStatement) (hspur : OsinLemma94CaseOneSpurStatement) : OsinLemma94CaseOneXPocketStatement`.
  - A spur walk goes to `hspur`.
  - Otherwise `pocketInputs_X` makes the walk noncrossing with a following complement cycle. A relator cell is inside
    by `listVal_outer_eq_one` on `ofNoncrossingClosedWalk`, Π is off the side, B is a carrier arc and `invDarts X` is
    short.
  - The enclosed loop cut and `false_of_below` finish.
  - This covers face bubbles, cell pinches, touches and simple walks at once. Under `hout`, cutting-path islands are
    spur walks.
- CLAIM `EnclosedFaceSetOfNoncrossingStatement` (combinatorial):
  - nodup, chain and closes by reversing the walk;
  - mem_iff from `IsNoncrossingClosedWalk.outerCycle` `cycle_mem_iff`;
  - turn_mem from `BoundaryCycle.boundaryWalk_next` on the following outer cycle, where internal darts are off the walk
    edges.
  - Module: `GroupApproximation/GGT/VanKampen/ClosedWalkEnclosedNoncrossing.lean`.
- RESUME 20:15 after the ~20:03 outage. Records checked: 32910e583, bbe90003a and 70cf7175a are on main, and no probe of
  mine was pending. Ruling: the enclosed route (bbe90003a) is primary for the X-pocket. I own (2) and the Y twin; (1)
  goes to ms-traces-2 with ms-inverses-1, (3) to w1-binder-8.
- (2) `enclosedFaceSetOfNoncrossing` in `ClosedWalkEnclosedNoncrossing.lean`: `EnclosedNoncrossing.exists_sigma_pow_of_boundaryWalk`,
  `mem_of_first_kept`. First probe 0913-202655-75681 FAILED at one step: `simp only [IsBoundaryDart, …]` gave "Invalid
  simp theorem". It is replaced by `Iff.trans` plus `show` plus `mem_sideOutside_iff`, and the co-probe is running.
- Y twin: ms-intro-3's `osinLemma94CaseOneYPocketOf_of_xPocketOf` (on origin, the swap of the connector pair) gives
  every Y shape statement from the X one, so the twin is a composition. CLAIM
  `GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94SameCellPocketNoSpur.lean` (path free):
  `osinLemma94CaseOneNoSpurXPocket_of_enclosedLoopCut` and `...NoSpurYPocket...` over `hloop` alone, plus
  `osinLemma94CaseOneXPocket_of_enclosedLoopCut` and `...YPocket...` over `hloop` and `hspur`. The interface was sent to
  w1-binder-8, whose `_of_enclosed` assembly is its own.
- Excision route check (before any Prop): `sideFaces` crosses every non-walk edge. Removing the lobe's edges can join a
  pocket face to f, and so to the exterior, when the walk crosses at the lobe vertex. So "the exterior stays off the side"
  needs a noncrossing walk. `SameCellPocketNoncrossing.pocketInputs_X` (on origin) gives noncrossing only at s = x with no
  spur. Island: ms-traces-2 (enclosed singular subdiagram) and w1-binder-2
  (bridge component map) are building (a).
- Audit sent to ms-traces-2:
  - `DiscDiagram.ofPlanar` gives Ξ; `exists_relatorCells_of_planar` gives the cells; `ofPlanar_rCellCount` gives the
    counts; `isRelatorProduct_of_planar` gives the value.
  - Missing: `Δ.LeastArea → Ξ.LeastArea` for a singular F. `LeastArea.length_filter_mem_le` needs `IsDiscRegion`.
  - InnerDiscRegion and the zero-cell merge do not apply.

## State

Every sentence of tex 1–165 is carried by a closed declaration or honestly classified. The exceptions:
- a16637da7249 (abstract, torsion-free clause) stays partial on W1;
- the three new modules (KorchaginLiteralSentence, IntroCompressorCentralizerSentence, IntroMFDefinitionCoronaBridge) await
  root wiring.
Residual statements owned by this lane: none.
