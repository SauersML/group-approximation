# ms-cite-1: literature-input ledger for `non_mf_groups_exist.tex`, tex 1–1337

Lane `ms-cite-1` (session nonsofic-existence-49, wave 2), 2026-09-13. Tex at origin/main 835fa3ee5, whose tex
equals 68481e4d7.

## Method

- Every `\cite` in tex 1–1337 (47 citing sentences) was joined by sentence text to its row in
  `metadata/NON_MF_SENTENCE_MAP.tsv` through `metadata/NON_MF_SENTENCE_CENSUS.tsv`.
- Every carrier the row names was checked on origin/main:
  - root reachability: the import closure of `GroupApproximation.lean`, 6530 modules;
  - its audit lines, `#audit_closed_axioms` or `#audit_axioms` (one- and two-line forms, 9239 names);
  - the statement text of each carrier audited only with `#audit_axioms`.
- The carrier modules were scanned for the quarantined package names in `metadata/LITERATURE_QUARANTINE.md`.

## Verdict

- Every cited result that a proof in tex 1–1337 uses is PROVED in Lean: closed, root-reachable, no literature
  binder. There is one exception: **Hull's small cancellation theorem**, still assumed through the W1 wall on
  the thm:torsion-free rows (see "Still assumed").
- Census defect: row `b1b04e376fe7` names the wrong carriers. The correction is in
  `metadata/nm-census-rows/ms-cite-1.tsv`.
- Three formalized rows had carriers with binder-free statements but no closed audit.
  `Manuscript/NonMFSentences/CitationSweepIntroAudit.lean` adds `#audit_closed_axioms` for them (probe pending).

## Proof steps and asserted results

| tex | cite | row | carrier on main | verdict |
|---|---|---|---|---|
| 87–98 | CDE (MF group definition) | 88e8012cb87e formalized | `OneSidedMFRadical.manuscriptIntroductionMFDefinition` (closed) | proved |
| 98–102 | Korchagin Props 2, 7 | b1b04e376fe7 formalized | `NonMFSentences.KorchaginSentence.manuscriptSentence_korchaginFullSequenceSeparation : ∀ countable G, IsOperatorMF G ↔ Nonempty (WeakMFApproximation G)` (closed, root). **The map row names the strong-convergence carriers of the next sentence instead** | proved; row corrected |
| 102–105 | GaoEtAl, Schafhauser | 837b7cffa562 formalized | `not_isStronglyOperatorMF_of_not_isOperatorMF` (its only premise is the sentence's own) | proved |
| 115–116 | BK (MF algebra) | ad33e493e32f formalized | `manuscriptArbitraryPositiveDimensionAlgebraMFDefinition` (closed) | proved |
| 151–153 | Khanh–Thanh Prop 4.2, Cor 4.4 | 8766dc520cfb formalized | 3 of 3 carriers closed | proved |
| 273–274 | Elek–Szabó Thm 1 | f969236a73d8 formalized | `AmenableTraceTheorem.manuscriptWSoficFromLocallyRFExtension` (closed) | proved |
| 274–282 | Brown, STW (question), TWW | a96c09324a87 formalized | the used content "C*_max(W) is not nuclear" is `manuscriptSentence_maximalCStarWNotNuclear`; no proof consumes TWW | proved; TWW is context |
| 284–286 | Korchagin Cor 10, Prop 13 | 2a97fb901bad formalized | `manuscriptShiftKernelIsOperatorMF : IsOperatorMF ShiftKernel` via `isOperatorMF_of_isLEF`, `isLEF_of_locallyResiduallyFinite` | proved; closed audit added |
| 286–288 | Korchagin (question) | cd3ea932e46a formalized | `manuscriptMFNotClosedUnderIntSemidirect` (∃-statement) | proved; closed audit added |
| 321–325 | Lubotzky–Oppenheim, Thom | 6edef6dc2d68 formalized | `manuscriptSentence_positiveMFProblemAnswerMakesEveryCountableGroupMF` (closed, now root) | proved |
| 328–332 | MIPRE, Goldbring–Hart Prop 6.1, Rem 6.2 | abfcbcb3af2b formalized | `NonMF.PriorWork.printedNegativeConnesEmbeddingSentence`: the conclusion comes through the paper's reduced group algebra; the Connes-embedding route is credited context no proof consumes | proved; closed audit added |
| 464–466 | Akemann–Walter | 86ee71463acf definition | `manuscriptSentence_kazhdanProjection` (closed), `KazhdanData.projection` | proved |
| 518–520 | Akemann–Walter | 87f873612529 formalized | `TransportProjectionCommutation.exists_projectionData (KD : KazhdanData L)`; `KD` from `exists_kazhdanData` (root, from (T)) | proved |
| 752–753 | Akemann–Walter | 0546c4f445c0 definition | `KazhdanData.projection`, `StrictKazhdanCompression.proj/shift` | definition |
| 773–774 | BK (separable RFD ⇒ MF) | e4fcef4295ca formalized | `ResiduallyFiniteDimensionalMF.isMFAlgebra`, `MatrixCoronaFinite.mfAlgebra_isStablyFinite` (closed) | proved |
| 792–793 | Korchagin Cor 10 | 330d435b12e2 formalized | `manuscriptSentence_reductionModuloOddRFAndMF` (closed) | proved |
| 952–955 | EJZ Thm 1.1, BHV Thm 1.3.1 | 0939d33e1ff4 formalized | 4 of 4 closed; EJZ = `IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT` (via `ejz`); BHV = `KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT` | proved |
| 1065–1067 | EJZ | b45891d88426 formalized | closed carrier present | proved |
| 1098–1099 | EJZ | 057fe08fb3bb formalized | 2 of 2 closed | proved |
| 1160–1162 | GHW Thm 4 | b6d1590be7ab formalized | `GHW.printedGHWTheoremFour : ∀ field K, ∀ countable Γ ≤ GL_2(K), Haagerup` (closed, root) | proved at printed generality |
| 1169–1171 | EJZ | 3009704fef89 formalized | `EJZCitationSentences.manuscriptSentence_jacobsonThreeCoordinatesCarryPropertyT` (closed, two-line audit) | proved |
| 1179–1181 | Khanh–Thanh Prop 4.2, Cor 4.4 | 98115b8e2580 formalized | 2 of 2 closed | proved |
| 1187–1189 | EJZ, BHV | a71f65809e0b formalized | 5 of 5 closed | proved |
| 1192–1195 | Abrams–Aranda, Ara, Preusser Thm 3 | 2bf4b5aca1b4 formalized | `binaryLeavitt_isPurelyInfiniteSimpleRing`, `binaryLeavitt_isExchangeRing`, `BinaryExampleSentences.manuscriptSentence_purelyInfiniteExchangePreusserSandwich` (binders only N, hN) | proved |
| 1206–1207 | Aranda Pino–Crow Cor 4.3 | d38df1795c78 formalized | `BinaryLeavitt.center_eq_bot` (every field) | proved |
| 1223–1224 | AGP Def 1.2 | c0fe92a1903d definition | `IsInfiniteIdempotent`, `IsPurelyInfiniteSimpleRing` | definition |
| 1225 | Abrams–Aranda | 4fb6ccd3e134 formalized | `AryLeavitt.isPurelyInfiniteSimpleRing (hd : 2 ≤ d)`, every field | proved |
| 1244–1246 | AGP Cor 1.7 | 5c5eeda68a8a formalized | `manuscriptSentence_matrixRingAgainPurelyInfinite` (printed hypotheses only) | proved |
| 1247–1248 | AGP Thm 2.4 | 6c03d472e975 formalized | `MFQuotientUnitsKOne.agpUnitKappa` (closed) | proved |
| 1249–1250 | BK | 55adb8bf7a88 formalized | `CountableAbelianMFPrintedRoute.manuscriptSentence_countableAbelianIsMFPrintedRoute` (closed) | proved |
| 1256–1257 | AGP Prop 1.5 | df9b558e0cb8 formalized | closed | proved |
| 1269–1272 | AGP Thm 2.4 (proof), Prop 1.5, Cor 1.7; Menal–Moncasi | afe1782dc7bc attribution | `MFQuotientUnitsKOne.manuscriptAGPInputs : AGPMatrixReduction ∧ AGPUnitKappa ∧ AGPUnitKappaResidue ∧ AGPUnitK1 ∧ AGPMenalMoncasiReduction ∧ AGPStepOne` (closed) | every quoted fact proved |
| 1327–1329 | Khanh–Thanh Thm 7.2 (proof) | 4321530b3fec formalized | `KhanhThanhDiagonal.printedKhanhThanhDecomposition_everyArity`, `scalarSurjective_everyArity` (closed) | proved |

## Attribution and credit only (no proof consumes them)

| tex | cite | row |
|---|---|---|
| 153–154 | OAI Ch. 3 | 374637bc6ac7 |
| 225–226 | Leavitt | 4bf35a8f555d (definition of the algebra, closed carrier) |
| 310–312 | BK94 | 27d456b915c0 |
| 313–315 | BK (NF iff nuclear and MF) | 14ee41b7f3cc |
| 315–318 | BK question, TWW | 82cac0c03a39 |
| 319–321 | Goldbring–Hart §6 | ba77c51e9726 |
| 325–327 | CDE, Korchagin, BDL | c8241b12c037 |
| 336–339 | OAI Prop 2.3 | 213a6657c8ff |
| 339–342 | Kun, Kun–Thom | de554b7cd342 |
| 349–351 | OAI, FFF | b89e90ea6607 |
| 351–353 | BDL Prop 1.5 | 9e2046c330c8 |
| 354–356 | Eckhardt | a494a9e94d28 |

## Still assumed

- **Hull's small cancellation theorem** (tex 303–305, `\cite{Hull}`; FFF §2 names the construction), row
  27e0c2f96db3 (attribution). The thm:torsion-free statement rows in tex 295–306, including the torsion-free clause
  of the abstract, are `partial`. They rest on
  `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement` (hgreendlinger), which carries Osin's
  appendix. The other walls on that route (hbridge, hKO, hW) are closed.
  - Residual: the eight post-(A) waist binders, owned by the other swarm's W1 lanes, plus w1-binder-1..8.
  - The quarantine scan of carrier modules found only `TheoremC.LiteratureInputs`, on this same row.
- No other cited result in tex 1–1337 is assumed anywhere in a formalized row's chain.

## Lean

- `GroupApproximation/Manuscript/NonMFSentences/CitationSweepIntroAudit.lean` (new), LANDED c04133c00:
  `#audit_closed_axioms` for `manuscriptShiftKernelIsOperatorMF`, `manuscriptMFNotClosedUnderIntSemidirect` and
  `printedNegativeConnesEmbeddingSentence`.
  - Probe 0913-171556-18781 (base e24b2ae3b) was GREEN: a BUILT line for the module, and each of the three reported
    only propext, Classical.choice and Quot.sound.
  - The lead restart killed the local watcher before it wrote the evidence record. Re-probe 0913-172317-48724 on the
    same bytes (md5 f0275ed1…) was GREEN from the artifact cache and recorded the evidence nmland needs.
  - Queued for wiring in `wire-queue.txt`. Until it is root-imported, these closed audits certify the carriers but
    do not change the root closure.

## Truth audit of the post-(A) W1 waist binders (lead item, 2026-09-13 ~17:40, origin 97de60f05)

Method:
- Read each def on origin and the owners' truth audits (audit-sec3, systolic-counts, dgo-analytic, dgo-geometric,
  hull-euler, audit-intro, hull-count94, w1-binder-1..8).
- Hand models: degenerate ε, spurs and spikes, same-cell pockets, pinched two-gons, the section count.
- No new Lean: binder 7's model is already on origin, and no other cheap model exists.

Binders 1 and 3–6 carry the prefix `∃ ε₀ ∀ ε ≥ ε₀ ∃ ρ₀ ∀ ρ ≥ ρ₀ ∀ W, OsinCCondition D W ε μ λ c ρ →`. That prefix rules out
the cheap degenerate-ε models that refuted binders 2 and 7, which quantify every ε. Binders 7 and 8 have no small
cancellation prefix at all.

| binder | Prop (origin) | verdict | evidence |
|---|---|---|---|
| 1 | `OsinLemma94ClassCountInput` (PolygonClasses:360): ∃ K M L, ∃ Q, `ClassBudget K ∧ ClassCovers M L` | TRUE-plausible | audit-intro's model tests pass both halves. The suspected gap is absent: `SectionCuts.count_le : count ≤ 4` (OsinAppendixSections:152) gives \|family\| ≤ 3(n+3) ≤ 12n, so the same-cell slack ⌈c/λ⌉₊(n + 2\|family\|) ≤ 25⌈c/λ⌉₊·n, w1-binder-2's `T n`. `OsinCCondition` has no reducedness clause, so spikes across their own cell are admissible and unbound, but they cost O(1) per cut (at most four cuts), and inside a section two regions merge through the spike. Route: w1-binder-2's `classCovers_of_sameCellFactor` (2336592ee) with hypotheses (i) e3bbcf801 and (ii) planned, M = ⌈1/λ⌉₊ + 1 |
| 3 | `OsinLemma94CaseOneSameCellStatement` (CaseOneFace:476) | TRUE-plausible, not circular | systolic-counts' sketch. Cell-free pockets are killed by `false_of_sameCell_cellFree_pocketRegion_X/_Y` (29c1eeae3). A pocket with a relator cell gives a loop cut, then `OsinLoopCut.false_of_below`. Its `hb` is the `OsinLemma97Below … Δ.rCellCount` binder, the induction hypothesis, so there is no circularity. Consumes binder 8 and the pocket region from the walk |
| 4 | `OsinTwoGonHoldsSectionStatement` → `TwoGonHoldsInput` (EulerSmallFaces:94) | TRUE-plausible, not circular | audit-sec3 (true, orientation right). The conclusion is `False`, so it is O-invariant, and the three configurations with no pocket on `S.diagram` ((a) section backtrack, (b) source-gap edge with cell i on both sides, (c) annulus) are handled on copies inside the proof. w1-binder-4's noncrossing route bypasses the pinch |
| 5 | `OsinMultipleEdgePocketRegionSectionStatement` → `MultipleEdgePocketRegionInput` (RegionSide:49), on `S.diagram` | **CIRCULAR as spelled** | audit-sec5's configuration (b′) (a spur on Π_i between C1, C2 longer than 2ε) has no `P` on `S.diagram`. Excluding it from an optimal family needs Lemma 9.7(b) itself (lead 15:45; dgo-analytic's lake model kills only `a ∪ gap ∪ b`). Corrected: hull-select's R1 copy form (draft `nm/drafts/hull-select-RegionSide-copy-r1.lean`): `∃ X, Nonempty (OEquivalentDiscDiagram Δ X) ∧ legal labels ∧ ∃ P C i' j' s₁ s₂ A₁ A₂, …`, norms ≤ ε, both `FollowsBoundary`. Plausible; its producer needs the cell-to-cell pinch Prop, which needs the ∃ε₀ prefix or `0 < ε` (wrap-rose shape) |
| 6 | `OsinSectionPocketFaceSetSectionStatement` → `SectionPocketFaceSetInput` (Pieces:228) | TRUE-plausible | Already on an O-equivalent copy with legal labels. The conclusion ties `K` to the hypotheses only through `ε` and the positions of section j. Hand checks: an empty pocket merges `a ∪ pocket ∪ b` (zero-cell merge); the pocket on the section-j side keeps its target arc inside `[cut j, cut (j+1))`, so there is no wrap. Producer: kh-ejz's `exists_pocketFaceSet_of_exteriorAt_of_value` (336b8afeb) over `CopyClean` (w1-binder-6: five copies still unproduced) |
| 7 | `PocketPinchLabelledStatement` (Pieces:272) | **FALSE, model on origin** | `OsinPocketWrapRose.pocketPinchWrapRefutation` (87358b0ad, `#audit_closed_axioms`, probe 0913-163031-39703 GREEN): a three-petal rose at ε = 0 with one-letter words. The def block is byte-identical to the refuted one (md5 61b753de). Corrected: `PocketPinchLabelledPosStatement` (`0 < ε`, 1b4736bcb); waist form `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsPos` (4db9c6729). Truth at ε ≥ 1 open; the rose is rescued (`wrapRoseRescue`, closed) |
| 8 | `GeodesicCollarStatement` (SurgeryGeodesicCollar:67) | TRUE-plausible | audit-sec3 (paper sketch), dgo-geometric (no refutation). Hand checks: `s = []` forces `g = []` and is `geodesicCollarOutput_nil`; `g = rest = []` is excluded by hypothesis; `g = []` with `s ≠ []` identifies the distinct ends of the simple walk inside the strip. The only residual is `StripStepStatement` (w1-binder-8, kh-torsion) |

Sent to main: binder 7 (FALSE) and binder 5 (CIRCULAR), each with the corrected spelling.

## Counterexample search for the corrected binder 7 at ε ≥ 1 (lead item, 2026-09-13 ~18:05)

Target: `PocketPinchLabelledPosStatement` (`Estimating/OsinPocketPinchPositive.lean`, 1b4736bcb), i.e. binder 7 with
`0 < ε`. Scope agreed with w1-binder-7: this lane does the counterexample search; w1-binder-7 keeps the positive route
(`OsinPocketFullArc`, `OsinPocketArcTrim`, the step).

**No counterexample found; the question is unsettled at ε ≥ 1.** (Corrected ~18:35 after w1-binder-7's check: the
in-place re-decomposition rescue first recorded here is wrong.)

What a counterexample would have to be. The Prop has NO `OsinCCondition` binder, so a refutation is one concrete diagram
`X`, positions `lo, hi`, and a pocket face set `K` in walk order (`K.ClosedWalk`) whose every O-equivalent copy has no
simple pocket face set at `(lo, hi)` — the exact shape of the rose. The rose's refutation
(`OsinPocketWrapMonogon.no_simple_of_oEquivalent_monogons`) is driven by the ε = 0 length invariant: sides must have
length ≤ 0, so `s₁ = s₂ = []`, each arc has at most one dart, and the boundary cycle collapses to a loop or to nothing.
At ε ≥ 1 that invariant is gone; a side may carry a dart.

What is known at ε ≥ 1.
- **The rose itself:** `wrapRoseRescue` (kept `{R}`, `s₁ = [5]`, empty arcs), closed on origin.
- **A monogon relator cell with a second relator cell:** `{R}` with its one dart as `s₁` is a simple pocket face set at
  ε ≥ 1 (w1-binder-7, paper).
- **The long analog over `F(a,b)` with boundary letter `c = aᴺbᴺ`** (w1-binder-7's paper rescue): rescued only through a
  rebuilt O-equivalent copy. Shorten the source arc to `N−1` darts, make the trimmed letter one side and the `c`-dart the
  other.

**Correction: in-place lobe re-decomposition is not a rescue.** On the long rose at ε = 1, N = 3 (w1-binder-7):
`Π = aᴺ`, `R = bᴺ`, the exterior is one dart `c = aᴺbᴺ`, and `κ` is a G-face walking `inv(∂Π)`, then the c-loop, then
`inv(∂R)`, all at one vertex `v`; `K = {κ, R}` with `t₁ = ∂Π`, `t₂ = [c]`, empty sides. No face set of X itself is a
simple pocket face set:
- `{Π}`, `{R}`: every dart faces `κ`, so both arcs are empty and the sides would need `N > 2ε` darts;
- `{κ, R}`, `{κ, Π}`: the boundary is `inv(∂Π)` (or `inv(∂R)`) plus the c-loop at `v`, so any walk order visits `v` twice;
- `{κ, Π, R}` leaves no source cell; `{κ}` holds no relator cell.

The lobes of the pinched cycle are simple walks, but a simple closed walk bounds a pocket face set only if its pocket
side excludes the exterior and some relator cell, and it splits with sides ≤ ε. The `inv(∂Π)` lobe's side
`{κ, R, ext}` contains the exterior; the c-loop's side `{κ, Π, R}` holds every relator cell. So a witness can require a
rebuilt copy.

Consequences:
- The nested-petal, touching-remainder and repeated-vertex candidates, and w1-binder-7's stuck configuration (a full
  arc with a nonempty remainder and both sides at exactly ε), are NOT shown rescued.
- The ε = 0 length invariant (`no_simple_of_oEquivalent_monogons`) does not lift to ε ≥ 1 as it stands, since a side
  may carry a dart. A refutation at ε ≥ 1 needs another invariant of O-equivalence that survives rebuilt copies.
  `OEquivalentDiscDiagram` (`RelativeGreendlinger.lean:123`) fixes only the boundary word and the relator words, and van
  Kampen values do not separate pinched from simple face sets (w1-binder-7).

**Verdict: unsettled at ε ≥ 1.** No counterexample found and no cheap `decide`-sized refutation; no rescue mechanism is
proved beyond the individual copies above. I built no new model.

## Binder 5 made non-circular, additively (lead item, 2026-09-13 ~18:15; LANDED eb678c70a)

hull-select's r1 copy forms never landed. They are ported into new modules; no existing module is edited. Nothing on
origin stated the copy form before (checked at ddc52231a). Boundary agreed with w1-binder-5 in one message: this lane
states and consumes the copy Prop; w1-binder-5, ms-intro-2 (step 5) and ms-intro-4 (step 6) produce it. At
w1-binder-5's request the copy is of `Δ`, not `S.diagram`: its producer outputs another optimal family over `Δ`.

Probe 0913-183303-64587 GREEN at base 69fe92a83, BUILT for both modules. Both modules are new, unwired and wire-queued.

`Estimating/OsinPocketMultipleEdgeCopy`:
- `MultipleEdgePocketRegionCopyInput`: the region data of `MultipleEdgePocketRegionInput` on an O-equivalent copy `X` of
  the least-area diagram with letter labels, with both `FollowsBoundary` clauses (R1), side norms ≤ ε and no length
  bounds.
- `MultipleEdgePocketRegionInput.copyInput`: the old form gives the copy form, witness `S.diagram` with `S.equiv`.
- `multipleEdgeCutInput_of_copyPieces`: the copy form, the collar and the cell transport give `MultipleEdgeCutInput`,
  through `nonempty_osinMultipleEdgeCut_of_pocketRegion`.
- `CellPocketWalkOuterOffSideStatement` and `CellPocketWalkSideRelatorCellStatement`, both stated, not proved: for the
  clean cell pocket walk of `CellPocketWalk.exists_clean_of_copy`, the exterior is off `sideFaces K.walk` and a relator
  cell is on it.
- `multipleEdgePocketRegionCopyInput_of_pinch` (at `0 < ε`): `exists_clean_of_copy`, then `CellPocketWalkColour.walk_orient`,
  then `CellPocketWalk.exists_cellPocketFaceSet_closedWalk_of_orient`, then ms-intro-4's
  `CellPocketFaceSet.copyRegion_of_pinch` (a0ef02fff), composed with `S'.equiv`.
- `OsinMultipleEdgePocketRegionCopySectionStatement` (∃ε₀ ∀ε ∃ρ₀ ∀ρ `OsinCCondition` prefix);
  `OsinMultipleEdgePocketRegionSectionStatement.copySection`; `osinMultipleEdgePocketRegionCopySection_of_pinch`
  (ε₀ = ρ₀ = 1); `osinMultipleEdgeCutSection_of_copyPieces`.

`Estimating/OsinGreendlingerResidualsV2Copy`:
- `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2CopySection`: ct-bilateral-cell's `_of_residualsV2`
  (ffd56be61) with binder 5 as `OsinMultipleEdgePocketRegionCopySectionStatement`.
- `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2Copy`: binder 5 replaced by four named residuals,
  `CellPocketCopyCleanStatement`, `CellPocketWalkOuterOffSideStatement`, `CellPocketWalkSideRelatorCellStatement` and
  `CellPocketPinchPosStatement`, through `copyRegion_of_pinch`.
- `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2_of_copy`: `_of_residualsV2` follows through `copySection`,
  so the copy waist asks for no more.

Residuals of binder 5 now:
- `CellPocketCopyCleanStatement`: w1-binder-5;
- `CellPocketPinchPosStatement` (at `0 < ε`): ms-intro-4;
- `CellPocketWalkOuterOffSideStatement`: w1-binder-3, per main;
- `CellPocketWalkSideRelatorCellStatement`: ms-inverses-2, per main (`cellPocketKeptCellNoncrossing` probing).

This lane claims none of them.

**Order assembly (LANDED da5b1466e, probe 0913-193950-9332 GREEN; supersedes the bdd0000bb spelling below).**
- `CellPocketWalkOuterOffSideSomeOrderStatement` is respelled in place to w1-binder-3's two-walk shape. It ranges over
  `RealizedSectionFamily`, with `K₁` for the order `(a,b)` and `K₂` for `(b,a)` between the same cells, and no
  CopyClean. The earlier `(b,a,j,i)` disjunct is the same walk as `(a,b,i,j)`, rotated.
- New: `CellPocketCopyCleanBothOrdersStatement`. It is needed because CopyClean's side fields differ between the two
  orders.
- Removed: `CellPocketWalkSideRelatorCellBothOrdersStatement` (over-strong, no users). The side relator cell of the
  chosen walk comes from ms-inverses-2's proved `cellPocketKeptCellNoncrossing`.
- `Estimating/OsinPocketMultipleEdgeCopyOrder`:
  - `copyRegion_of_offSideWalk` and `multipleEdgePocketRegionCopyInput_of_pinchOrder` build the region data from the
    walk with the exterior off its side;
  - `osinMultipleEdgePocketRegionCopySection_of_pinchOrder`, and the waist
    `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2CopyOrder`.
  - Residuals: CopyCleanBothOrders, the some-order outer statement, `CellPocketWalkEitherFollowsStatement`,
    `CellPocketPinchPosStatement`.

**Section spelling model test (paper, 2026-09-13 ~19:45).** `PocketPinchLabelledSectionStatement` (d07c38405,
w1-binder-7): no counterexample.
- The x^ε family has a full t₁, so the proper-t₁ premise excludes it.
- Proper t₁ at ε = 1 with a one-letter boundary gives three shapes:
  - (a) conjugator separation `c = xPx⁻¹yQy⁻¹`: no proper-t₁ K exists (`xPx⁻¹ = β⁻¹pα⁻¹` is too short);
  - (b) no separation `c = PxQx⁻¹`: K exists, and K′ = (z⁻¹, P minus its last letter, c) with t₂ = [] rescues it;
  - (c) non-adjacent side letters: no two-cell X exists, by conjugacy.
- Untested: extra relator cells supplying non-adjacent side letters.

**Some-order respelling (LANDED bdd0000bb, probe 0913-191314-53572 GREEN).** w1-binder-3 showed the fixed-order
outer-off-side statement is over-strong (042fb1881): the exterior lies in at most one of the two complementary pockets.
New statements in the same module:
- `OuterOffSideForOrder S a b i j` and `SideRelatorCellForOrder S a b i j` (per-order predicates);
- `CellPocketWalkOuterOffSideSomeOrderStatement` (the exterior is off the side in order `(a,b,i,j)` or `(b,a,j,i)`;
  owner w1-binder-3);
- `CellPocketWalkSideRelatorCellBothOrdersStatement` (owner ms-inverses-2). This is probably over-strong: per order,
  `cellPocketKeptCellNoncrossing` needs the exterior off that side and one cycle following its boundary, and the latter
  fails on an 8-dart model (ms-inverses-2). The assembly should consume `OuterOffSideForOrder → SideRelatorCellForOrder`
  for the chosen order.
- `_of_residualsV2CopyOrder` is not landed yet. It waits on whether outer-off-side is proved at the original family or at
  the clean rebuild.

## Order assembly over the Euler residual (main ~20:40 and 21:22; LANDED 7a45179c4)

`Estimating/OsinPocketMultipleEdgeCopyOrderEuler` is additive; `OsinPocketMultipleEdgeCopyOrder` is unchanged, per main's
Rule 22 ruling (no edits to ct-rank-two-limit's V4 files). It has four declarations: `copyRegion_of_offSideWalkEuler`,
`multipleEdgePocketRegionCopyInput_of_pinchOrderEuler`, `osinMultipleEdgePocketRegionCopySection_of_pinchOrderEuler` and
`relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2CopyOrderEuler`. They take ms-inverses-2's
`CellPocketWalkEulerStatement`. Its two Euler equalities make `PocketRegion.ofNoncrossingClosedWalkEuler` a pocket region
on the walk, and `exists_kept_of_cellPocketRegion_of_leastArea` then puts a relator cell on its side. Probe
0913-203827-69476 GREEN. ct-rank-two-limit consumes it in `OsinGreendlingerWaistV4Euler`.

## The positive cell pinch is false (main 23:12; LANDED e0a0776bb)

**Verdict: `CellPocketPinchPosStatement` is false as stated.** `OsinPocketCellPinchRose.cellPocketPinchRoseRefutation :
¬ CellPocketPinchPosStatement.{0, 0, 0}` is in `Estimating/OsinPocketCellPinchRefutation`. Probe 0913-234315-3209 is
GREEN, and `#audit_closed_axioms` passes.
- `CellPocketWrap.not_simple_of_monogon_first`: at every ε, a cell pocket face set whose first cell has one dart `x` is
  not simple. The arc `t_1` is `[x]`, `x` is a loop, and the nonempty rest `s_2 t_2` starts where `alpha x` starts.
- `no_simple_of_oEquivalent_monogons_pos` and `not_cellPocketPinchPosStatement_of_monogon_cells`: an O-equivalence keeps
  word lengths, so a diagram on one-letter relators with a cell pocket in walk order at `0 < ε` refutes the Prop.
- The carrying diagram is a four-petal one-vertex rose: `κ = [0,2,4,6]`, cells `[1]`, `[3]`, `[5]`, exterior `[7]`. The
  face set `{κ, R}` has cycle `[0,6,2]` at ε = 1; the exterior-facing dart `6` is the second side. ms-intro-4's ε = 0
  calibration (52eb75920) built no carrying diagram.
- Replacement for V4 residual 8, sent to ct-rank-two-limit and w1-binder-7: `CellPocketPinchSectionStatement` (d3b0769b8),
  via `copyRegion_of_pinchSection`. Threading it needs thresholds from the section statement, least area of the copy, and
  a new named proper-arcs residual for the cell walk. That residual needs `OsinCCondition` and a model test; it fails on
  monogon relators.

## Binder 5 from the section cell pinch (main ~02:0x; on origin, re-probing after the 08:4x reboot)

`Estimating/OsinPocketMultipleEdgeCopyOrderSection` is additive. It has four declarations:
`CellPocketWalkProperArcsInput`, `CellPocketWalkProperArcsSectionStatement`, `copyRegion_of_offSideWalkSection` and
`multipleEdgePocketRegionCopyInput_of_pinchSectionOrderEuler`, plus
`osinMultipleEdgePocketRegionCopySection_of_pinchSectionOrderEuler`.
- The copy is built as `CellPocketWalk.toCellPocketFaceSetOfNoncrossing`, whose arcs are the walk's arcs by `rfl`.
- Least area comes from `S.equiv.leastArea`, and the thresholds are the max of those of the section cell pinch and of the
  proper-arcs residual.
- V5 (`OsinGreendlingerWaistV5`) consumes it as residual 8.

**Model test of `CellPocketWalkProperArcsSectionStatement` (2026-09-14). Verdict: true through Lemma 9.7(b) at fewer
cells, and not provable as spelled.**
- A full first arc makes b's arc on `Π_i` end where a's arc begins. Every dart of `∂Π_i` is then on the walk, so `Π_i`
  is a lake of the complement, meeting it at one vertex.
- Neither `CellPocketWalk.CopyClean` nor the Euler and exterior-off-side facts exclude that lake.
- Filling it gives `Q` with boundary `s_1 s_2 t_2⁻¹`, holding `Π_i` and `R`, with fewer cells than `Δ`. Clause (b) on `Q`
  needs contiguity `> 1 − 13μ` to `∂Q`, but the sides are short and `t_2` is a piece of `Π_j`. So no counterexample
  exists under `OsinCCondition`.
- The proof needs `OsinLemma97Below … Δ.rCellCount`, which the prefix does not supply.
- Recommended additive respelling: `CellPocketWalkProperArcsBelowInput`, threaded through a below variant of the
  multiple-edge cut input. `osinLemma97_atParameters_of_inputs` holds `hbelow` where it consumes `hmulti`
  (OsinAppendixSectionInduction:182–205).
- Open build pieces: `Q` as a following pocket region, since its walk need not be simple, and side norm `2ε` against
  `false_of_pocketRegion_of_below`'s `≤ ε`.

## CLAIM (main's ruling, 2026-09-14 ~09:0x): the below-Δ chain for binder 5

ms-cite-1 owns the whole chain, additively; the induction module's owner is down. The chain:
1. `MultipleEdgeCutBelowInput D λ c μ ε W`: the multiple-edge cut producer with an `OsinLemma97Below … Δ.rCellCount`
   premise.
2. Below variants of every consumer of `hmulti`, each applied where `hbelow` is already in scope:
   `exists_elevenCell_of_below`, `OsinSectionPocketCut.exists_large_region`, `descentInput_of_sectionPocketCut`,
   `osinLemma97_atParameters_of_inputs`, the section bundles `OsinSection97InputsStatement` and
   `OsinSection97PocketInputsStatement`, and `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketParts`.
   Module `Estimating/OsinAppendixSectionInductionBelow`.
3. The binder-5 below variant: `MultipleEdgePocketRegionCopyBelowInput`, `multipleEdgeCutBelowInput_of_copyPieces` and
   the section statements.
4. `CellPocketWalkProperArcsBelowInput` and its section statement, with the order producer over w1-binder-7's
   `CellPocketPinchSectionDistinctStatement`, passing `hij`. Module `Estimating/OsinPocketMultipleEdgeCopyBelow`.
5. Then the proof of the below input: `Q` = side ∪ `Π_i` as a following pocket region, and a `2ε` variant of
   `false_of_pocketRegion_of_below`.
Names go to ct-rank-two-limit for V6 when they land.

**Items 1–4 built** (probe 0914-085136-43184 GREEN, BUILT for both modules).
- `OsinAppendixSectionInductionBelow`: `MultipleEdgeCutBelowInput`, `MultipleEdgeCutInput.toBelow`,
  `exists_elevenCell_of_below_multiBelow`, `OsinSectionPocketCut.exists_large_region_multiBelow`,
  `descentInput_of_sectionPocketCut_multiBelow` and `osinLemma97_atParameters_of_inputs_multiBelow`.
  The section assemblies: `OsinSection97InputsBelowStatement`, `osinLemma97Section_of_inputsBelow`,
  `OsinSection97PocketInputsBelowStatement`, `osinSection97Inputs_of_pocketInputsBelow`,
  `osinLemma97Section_of_pocketInputsBelow`, `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketInputsBelow`,
  `OsinMultipleEdgeCutBelowSectionStatement`, `OsinMultipleEdgeCutSectionStatement.toBelow`,
  `osinSection97PocketInputsBelow_of_parts` and `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketPartsBelow`.
- `OsinPocketMultipleEdgeCopyBelow`: `CellPocketWalkProperArcsBelowInput` with its section statement and `toBelow`,
  `MultipleEdgePocketRegionCopyBelowInput`, `OsinMultipleEdgePocketRegionCopyBelowSectionStatement`,
  `copyRegion_of_offSideWalkSectionBelow`, `multipleEdgePocketRegionCopyBelowInput_of_pinchSectionOrderEuler`,
  `osinMultipleEdgePocketRegionCopyBelowSection_of_pinchSectionOrderEuler`, `multipleEdgeCutBelowInput_of_copyPieces`
  and `osinMultipleEdgeCutBelowSection_of_copyPieces`. It consumes `CellPocketPinchSectionDistinctStatement` and passes
  `hij`.

**Item 5 is open, with a gap beyond the plan.** Proving `CellPocketWalkProperArcsBelowInput` through the filled lake `Q`
needs two things.
- `Q` as a pocket region with both cycles following. The loop cut (`nonempty_osinLoopCut_of_pocketRegion`) and the
  two-arc cut (`nonempty_osinLoopCut_of_pocketRegion_twoArcs`) glue collars along following cycles.
  - w1-binder-6's `OsinPocketFullArcLakeModel` shows the complement cycle of a full source arc in a lake does not follow.
  - `OsinPocketFullArcLakeGlueModel` shows the Euler equality does not replace following for gluing.
  - `Q`'s walk `s_1 s_2 t_2⁻¹` need not be simple, and no one-arc loop pinch (non-simple walk to simple copy) is on
    origin.
- A side of norm `2ε` against the `≤ ε` of the cut builders.

**Item 5 re-ruled by main (~09:2x): reduce over the component-route transports, not a following-based loop pinch.**
- w1-binder-6 (09:1x) confirms that no cut builder without following cycles exists. Its transports
  `PocketCellTransportEulerStatement` and `PocketOuterTransportEulerStatement` (`X.LeastArea →` in place of
  `P.outer.FollowsBoundary →`, over `PocketGlueComponentPlanarStatement`, 53a33bef9) are planned in
  `Estimating/OsinPocketGlueComponentTransport`.
- In `nonempty_osinMultipleEdgeCut_of_pocketRegion`, following enters at two places: the collar step
  `exists_twoCollars_of_ne_or`, which takes and returns following cycles, and the cell transport, reached through
  `fourSectionCuts_cellTransport` with `hout`. `OsinMultipleEdgeCut.ofPocketRegion` needs no following.
- w1-binder-6 design note (09:3x): its Euler transports take `a.2.sourceArc.length ≠ 0`, because a degree-0 region can
  sit on a dropped component. So the builder produces `OsinMultipleEdgeCutNonzero` (`Estimating/OsinMultipleEdgeCutNonzero`,
  probing). It is the cut with transports asked only for regions with a nonempty source arc. Its
  `false_of_below` bounds a degree-0 region by `μ` without a transport, and it has an `ofPocketRegion`. The binder-5 Euler
  route then gives `MultipleEdgeCutBelowInput` ex falso under `hbelow`, with no new induction cascade.
- The collar half, probe 0914-100340-25986 GREEN: `Estimating/OsinPocketTwoCollarsEuler` states the named residual
  `GeodesicCollarEulerStatement`, the collar on a least-area pocket region with no following hypothesis and no following
  output, and proves `PocketRegion.exists_twoCollars_of_ne_or_euler` over it.
- Once the transports land: an Euler variant of `fourSectionCuts_cellTransport`, and
  `nonempty_osinMultipleEdgeCut_of_pocketRegionEuler`.
- Then binder 5's cut comes directly from the walk's Euler region `PocketRegion.ofNoncrossingClosedWalkEuler`, with no
  pinch and no proper arcs. `CellPocketWalkProperArcsBelowSectionStatement` follows as a corollary, since the cut
  contradicts `hbelow`.

## Section pocket producer below the bound (agreed with ct-return-tower, 09:2x; LANDED ca182efb7, probe 0914-100340-25986 GREEN)

The collar half `OsinPocketTwoCollarsEuler` is verified at the same commit.

Also verified:
- `OsinMultipleEdgeCutNonzero`, LANDED 99d7032c9 (probe 0914-101012-50694 GREEN).
- `OsinPocketMultipleEdgeCopyEulerRegion`, on origin at 498add940 (probe 0914-102634-36803 GREEN, BUILT):
  `MultipleEdgePocketRegionEulerCopyInput`, `MultipleEdgePocketRegionCopyInput.toEuler`, `copyRegionEuler_of_offSideWalk`
  and `multipleEdgePocketRegionEulerCopyInput_of_order`. These give binder 5's pocket region from the Euler residual
  alone, with no pinch and no proper arcs.

Still waiting on w1-binder-6's transports for the Euler cut builder: Euler collar + Euler cell transport +
`OsinMultipleEdgeCutNonzero.ofPocketRegion`, giving the nonzero cut.

**CLAIM (main ~10:4x): the producer of `GeodesicCollarEulerStatement`.** It has no producer or owner. The closed
`geodesicCollarStatement_holds` (`SurgeryGeodesicCollarStripStep`) builds the strip one dart at a time and keeps the walk
a simple closed walk (`isSimpleClosedWalk_pinch`), and a lake breaks simplicity. So there is no bridge from the closed
collar; the Euler form needs its own strip argument. Until it has a producer, replacing waist leaves 8/9 by the collar
and transport residuals is only a reshape, and ct-rank-two-limit keeps the current leaves.

Scope (10:5x).
- `geodesicCollarStatement_of_strip` uses following only through `isSimpleClosedWalk_invDarts_outer`. Below it, everything
  is over simple walks: the `Strip.walk` field, `isSimpleClosedWalk_pinch`, edge doubling, `insert_walk`,
  `join_vertexOf_ne` and `join_walk`, and `ofSimpleClosedWalk`. That is about 1,900 lines.
- A lake repeats only its touch vertex, which lies in the rest. So the join's side-from-rest separation survives, and only
  nodup inside the rest fails.
- Port plan:
  1. a noncrossing walk plus separation of the side's vertices, as the strip invariant;
  2. noncrossing preserved through doubling, pinch, corner join and insertion;
  3. output through `ofNoncrossingClosedWalkEuler`, whose Euler equalities need transporting from the input pocket or a
     named piece.

**BLOCKER (11:0x): there is no machinery for lakes.** fff-quotient's noncrossing port of the collar (09-13, lane stopped)
consists of `SurgeryNoncrossingCollarWalk`, `…WalkSides`, `…Strip` and `…Join`. It asks that the reversed walk's outer
cycle follow its boundary (`OuterTurn`, via `outerTurn_iff_followsBoundary`), and a full-arc lake fails that
(`not_outerTurn_lakeCycle`). So the Euler collar for a lake is new surgery, not a port.

Options sent to main:
- (a) keep the V7 leaves, the distinct-cells section pinch and the below proper arcs;
- (b) collar surgery without `OuterTurn`;
- (c) the proper-arcs leaf lake-first, which needs the same machinery.
Recommended (a). Held pending the ruling.

`Estimating/OsinAppendixSectionPocketBelow` contains:
- `SectionPocketCutBelowInput` and `SectionPocketCutInput.toBelow`;
- `OsinSectionPocketCut.exists_large_region_pocketBelow` (at the pocket, with `hbelow.mono`) and
  `descentInput_of_sectionPocketCut_pocketBelow` (at `Δ`, with the descent premise);
- the assemblies `OsinSection97PocketInputsPocketBelowStatement`, `osinSection97Inputs_of_pocketInputsPocketBelow`,
  `osinLemma97Section_of_pocketInputsPocketBelow`, `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketInputsPocketBelow`,
  `OsinSectionPocketCutBelowSectionStatement`, `OsinSectionPocketCutSectionStatement.toBelow`,
  `osinSection97PocketInputsPocketBelow_of_parts` and `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketPartsPocketBelow`.

ct-return-tower produces `SectionPocketCutBelowInput` in its `OsinPocketInnerWalk`, which imports this module.

## ε = 1 refutation of the positional pinch: state

- Group half LANDED fa030acf6: `OsinPocketPinchPosModelsAlgebra` and `OsinPocketPinchPosModelsNoRescue`
  (`noRescueKeptQ`/`noRescueKeptP`: no relation `α p⁻¹ β = g r^{±1} g⁻¹` with `|α|, |β| ≤ 1`, `p` a proper arc of one
  relator, `r` the other).
- Diagram half LANDED 003676a4d (probe 0914-083742-12913 GREEN, BUILT): `OsinPocketPinchPosModelsDiagram`, 20 darts,
  `pinchDiagram` with letter labels, `pinchK` at ε = 1 in walk order with full source and target arcs.
- Universal half, `Estimating/OsinPocketPinchPosModels` (probe 0914-091613-62601 GREEN, BUILT, `#audit_closed_axioms`
  on `pocketPinchPosRefutation`). **Verdict: `PocketPinchLabelledPosStatement` is false as stated, at ε = 1.**
  - `eq_or_mem_of_cycle_mem_iff`: a cycle of reversed face darts closes up the face set.
  - `mem_T_of_wordNorm_le_one` and `listVal_ne_one_of_mem_pinchW`.
  - `false_of_simple`, in three steps:
    - the target arc is empty, by the full-arc lemma or the one-dart closure;
    - the source arc is proper, by the full-arc lemma or the reversed-boundary closure;
    - `ofSimpleClosedWalk` gives a pocket region whose diagram has one relator cell, and it is the kept cell. The kept
      word differs from the source word; the same relator is rescued by `α = a⁻¹`, `p = [b, a]`, `β = 1`. Its value
      relation is refuted by `noRescueKeptQ`/`noRescueKeptP`.
  - `pocketPinchPosRefutation : PocketPinchPosRefutation`, i.e. `¬ PocketPinchLabelledPosStatement.{0, 0, 0}`.

## State

Scope finished for tex 1–1337. The ledger and census correction landed at 09d4f6b3d, the audit module at c04133c00.
The only still-assumed cited result is Hull's small cancellation theorem, through the W1 wall, which other lanes own.
Current work: the diagram and universal halves of the ε = 1 refutation of `PocketPinchLabelledPosStatement`.
