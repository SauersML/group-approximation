# Lane ms-intro-2: tex 166–232 (eq:intrinsic-defect, eq:defect-functorial, eq:leavitt)

Lead: session nonsofic-existence-49 (wave 2). Line numbers are at origin/main 68481e4d7. Census rows are matched by
text against `metadata/NON_MF_SENTENCE_CENSUS.tsv`, whose line numbers are at the pre-chain-core hash.

CLAIM carriers for 9bab404c96c5, 6b5d4b5c3081, 29d7a8ccf93a, 270c3118af88 in module
`GroupApproximation/Manuscript/NonMFSentences/IntroCompressorSentences.lean` (path free on origin, disk and every lanes/*.files at 16:55).

## Ledger (15 rows)

| key | tex | status on main | verdict |
|---|---|---|---|
| 56d73653208a | 164–172 display eq:intrinsic-defect | definition: `printedDefect`, `printedDefectSet`, `manuscriptSentence40_printedDefect_display` | PASS: normal closure of `[ucu⁻¹, ℓ]` with `u ∈ compressionSet L`, `c` commuting with `L`, `ℓ ∈ L`, exactly as displayed |
| 50a97a1f5896 | 173 "For every homomorphism" | structural | PASS: lead-in; the display's content is carried by 51077cfd1fa7 |
| 51077cfd1fa7 | 174–180 eq:defect-functorial + "since …" | formalized: `manuscriptPrintedDefectFunctorial` | PASS: closed Prop for every homomorphism of groups in `Type`; the proof is the printed one clause for clause (`map_printedDefect_le`) |
| 270c3118af88 | 182–185 criterion summary | formalized: `manuscriptOneSidedCompressionCriterion` | GAP (form): the carrier's clause is `K ≤ manuscriptCoronaMFResidual G`; the sentence says K "dies in every MF image". Countability is inherited from thm:compression-criterion. Fix: closed Prop "every homomorphism from G to an MF group is trivial on K", assembled from the criterion and the residual calculus |
| 0b6c334de950 | 187 "The proof has two steps." | structural | PASS |
| a700a5798fd5 | 187–194 first step | formalized: 15 declarations | PASS (spot check): concrete statements in CompressionCriterionSentences and KazhdanTransportSentences; no literature binder in the signatures read |
| 2189c5b26e10 | 194–196 "Second, let K …" | structural | PASS: sets hypotheses only |
| e63d12558c72 | 196–199 corner compression | formalized: 3 declarations | PASS (spot check) |
| 61827aea7807 | 199–205 limiting trace + footnote | formalized: `manuscriptSentence_limitingTraceIsTrivialCharacter`, `manuscriptSentence_compressionOutlineFootnote`, `manuscriptNormalKazhdanRadical_ultrafilterRoute` | PASS: closed Props |
| 9bab404c96c5 | 207–208 stable letter of an ascending HNN extension | structural ("not used in any proof") | GAP (classification): the sentence asserts mathematics. Fix: closed Prop over Mathlib's `HNNExtension L ⊤ φ.range` for every group with property (T) and every proper injective endomorphism: `t ∈ compressionSet (of.range)` |
| 91310d39561c | 208–210 `e_ij(a)`, `EL_n(R)` | definition: `elementaryUnit`, `elementaryGroup`, `manuscriptSentence54_…` | PASS: `1 + single i j a`, closure of those units |
| 6b5d4b5c3081 | 211–215 pair `s,t` gives a compressor | formalized: `FullDefectRingSentences.manuscriptSentence_{compressorMatrix,intertwine,defectIsEverything}` | GAP (generality): all three carriers are stated over the universal ring 𝒞 only; the sentence is for every unital ring R with ts = 1. Fix: closed Prop over every ring, from the general `OneSidedCompressor` lemmas (`compressor_mem_compressionSet`, `compressor_mul_coreRoot`, `centralMark_commute_core`, `defect_eq`) and `FullIdempotent.elementaryGroup_normal_eq_top_of_full` |
| 29d7a8ccf93a | 215–219 universal ring 𝒞, EL₄(𝒞) maps with normally generating image | formalized: `manuscriptSentence_universalProperty`, `manuscriptSentence_imageOfBNormallyGeneratesELn`, `UniversalPair.UniversalPairRing` | GAP (closure): `imageOfBNormallyGeneratesELn` takes a section variable `Q : ProperlyInfiniteUnit R`, not the printed hypotheses. Fix: closed Prop for every countable ring with ts = 1 and 1 − st full and every n ≥ 2, through `RankDescent.ofFull` and `UniversalGroupB.exists_hom_normallyGenerating` |
| 0317786bea4d | 221–223 thm:full-defect-ring for every n ≥ 2 | formalized: `manuscriptPrintedFullDefectRingProgrammeAllCharacteristics` | GAP (carrier generality): the programme's theorem clause is `PrintedFullComplementaryIdempotents`, n ≥ 4. The printed n ≥ 2 is `FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics : PrintedFullComplementaryIdempotentsRankTwo`, already closed and root-reachable. Fix: census row re-pointed, no new Lean |
| 4bf35a8f555d | 225–231 L_{F₂}(1,2) and eq:leavitt | definition: `FullDefectRingSentences.manuscriptSentence_ringRelations` | DEFECT (wrong carrier): that theorem is the relation list of 𝒞 in the proof of thm:full-defect-ring, not the definition of the binary Leavitt algebra. Correct carriers: `BinaryLeavitt.Relation` (the five equations of eq:leavitt), `BinaryLeavitt.BinaryLeavittAlgebra` (the `RingQuot` presentation), `BinaryLeavitt.family`, `BinaryLeavitt.lift`, `UniversalLeavitt.BinaryLeavittAlgebra` (the F₂ specialization). Fix: census row re-pointed |

`\cite{Leavitt}` at tex 226 names the algebra; it is not used as a proof step.

## Item 2 (main, 17:15): help W1 binder 5

CLAIM binder 5 step 4, orientation of the cell pocket walk colouring:
`GroupApproximation/GGT/VanKampen/Estimating/OsinPocketCellWalkColour.lean`.
This is the cell analogue of cite-hull's `PocketWalkColour.walk_orient`. Planned declarations:
- `CellPocketWalkColour.walk_orient`
- `CellPocketWalkColourStatement` / `cellPocketWalkColour`
The module consumes jacobson's `OsinPocketCellWalk` and cite-hull's `OsinPocketWalkColour`. The split was agreed with
w1-binder-5 (its report, 17:40): it keeps step 3; step 5 goes to ms-intro-2 after step 4; step 6 waits on audit-sec5.

**Step 4 CLOSED: LANDED b0ab3a234** (probe 0913-173847-9529 GREEN at base 41d8c3b03, BUILT
`OsinPocketCellWalkColour`, empty error index; `cellPocketWalkColour` depends on [propext, Classical.choice, Quot.sound]).
The module is new, unwired and wire-queued.
```lean
theorem CellPocketWalkColour.walk_orient (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (ha : a ∈ S.family) (hb : b ∈ S.family) (hab : a ≠ b) (hai : a.JoinsCells i j) (hbi : b.JoinsCells i j)
    (K : CellPocketWalk D eps S.diagram i j)
    (hfirst : K.firstSide = b.sideFrom j) (hsecond : K.secondSide = a.sideFrom i)
    (h₁ : ∃ G₁, K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
    (h₂ : ∃ G₂, K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j)
    (hcol : ∀ d, ¬ (faceOf (alpha d) ∈ faces ↔ faceOf d ∈ faces) ↔ walkKeep M K.walk d) :
    ∀ d ∈ K.walk, ∀ e ∈ K.walk, (faceOf d ∈ faces ↔ faceOf e ∈ faces)
def CellPocketWalkColourStatement : Prop   -- the same over CellPocketWalk.exists_of_joinsCells, proved:
theorem cellPocketWalkColour : CellPocketWalkColourStatement.{u, w, v}
```
The helpers `mem_boundary_of_mem_sideFrom`, `cell_face_not_mem`, `exists_crossDart` and `walk_cases` need no `i ≠ j`.
No crossing into the outer face is needed. The Statement closes through `exists_of_joinsCells`, so no Prop is left
open and there is no vacuity risk. The abstract step `orient_of_sides` is already model-tested
(`OsinPocketWalkColourModels`).

Feeding the step: `ClosedWalkFaceColouring.isNoncrossingClosedWalk_of_orient hM hne hnodup halpha hchain hcloses
(fun _ hcol => CellPocketWalkColour.walk_orient S ha hb hab hai hbi K hfirst hsecond h₁ h₂ hcol)`, with `hchain hcloses`
from w1-binder-5's `exists_of_joinsCells_closedWalk` and `hnodup halpha` from its `walk_nodup_and_alpha_not_mem`
(e9d8d2faf).

CLAIM binder 5 step 5, the kept relator cell of the cell pocket (17:55), in two new modules:
- `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketCellMeetsContained.lean`:
  `RealizedRegionFamily.subset_of_not_disjoint_cellPocketRegion`, `CellPocketMeetsContainedStatement` /
  `cellPocketMeetsContained`
- `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketCellKeptCell.lean`:
  `GloballyDistinguishedSectionFamily.exists_kept_of_cellPocketRegion_of_value`, `CellPocketKeptCellStatement` /
  `cellPocketKeptCell`

**Step 5 CLOSED** (both modules new, unwired, wire-queued):
- **35700dfe9** `OsinPocketCellMeetsContained` (probe 0913-180013-76668, BUILT):
  `RealizedRegionFamily.subset_of_not_disjoint_cellPocketRegion`, `CellPocketMeetsContainedStatement` /
  `cellPocketMeetsContained`. If no relator word has value one, a selected region meeting a pocket region whose cycle is
  `K.walk` lies in it. A dart leaving the pocket is on the walk. On a side it is a boundary dart of `a` or `b`. On
  `t_1`/`t_2` it crosses into `Π_i`/`Π_j`, which is not a region face because its word has value `≠ 1`.
- **15e21098e** `OsinPocketCellKeptCell` (probe 0913-180502-96781 GREEN, BUILT; `cellPocketKeptCell` depends on
  [propext, Classical.choice, Quot.sound]):
  ```lean
  theorem GloballyDistinguishedSectionFamily.exists_kept_of_cellPocketRegion_of_value (S) (ha hb hab) (hij : i ≠ j)
      (hai hbi) (K : CellPocketWalk D eps S.diagram i j) (hfirst : K.firstSide = b.sideFrom j)
      (hsecond : K.secondSide = a.sideFrom i)
      (h₁ : ∃ G₁, K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i)
      (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
      (P : PocketRegion S.diagram) (hinner : P.inner.cycle = K.walk) :
      ∃ kept, (cell S.diagram kept).face ∈ P.faces
  theorem …exists_kept_of_cellPocketRegion_of_leastArea   -- the same with hlea : S.diagram.LeastArea
  def CellPocketKeptCellStatement : Prop   -- over exists_of_joinsCells: LeastArea → ∀ P, P.inner.cycle = K.walk → kept cell
  theorem cellPocketKeptCell : CellPocketKeptCellStatement.{u, w, v}
  ```
  Route: if P held no relator cell, `Surgery.InnerDiscRegion.ofPocketRegion` collapses it and absorbs every selected
  region meeting it. That includes `a` and `b`, whose arcs on `Π_i` lie on `t_1`. Their arc darts are pairwise distinct
  and lie on `t_1 ++ t_2`, so the weights add up to at most `|t_1| + |t_2|`. The merged face reads `t_1, s_2, t_2, s_1`:
  a contiguity region from `Π_i` to `Π_j ≠ Π_i`, and `false_of_disc_absorbed_section` gives the contradiction. The
  pocket needs no FollowsBoundary.
- Residual Props: none.
- First probe red at one tactic step: `rw [mergedGeometry_target]` in the section goal, where the target arc's type
  depends on the target. The fix refutes the `none` case inside the hypothesis.

Binder 5 now: steps 2–5 are closed on origin. Open:
- Step 6, the pocket face set, pinch, and region with both FollowsBoundary: audit-sec5 (15:25 ruling). Nothing is in
  flight for it and audit-sec5's last landing was 10:43.
- w1-binder-5's `CellPocketCopyCleanStatement`, stated, not proved. This is the cell analogue of `exists_kept_of_pocketRegion_of_value`: at least area, a
pocket region whose cycle is the walk holds a relator cell. Otherwise it absorbs the regions meeting it and
`false_of_disc_collapse_singleton` contradicts the distinguished choice.

## Item 3 (main, 18:1x): the `regions` field of binder 6's `CopyClean` split

The split was agreed with w1-binder-6 (reply 18:2x): ms-intro-2 owns `regions`; ms-binary keeps `cell_self` and does not take
`regions`; the order is outer-first, so the statement keeps the outer invariants of `OuterSideThickeningStatement`.

CLAIM `regions` thickening (18:30), in new modules:
- `GroupApproximation/GGT/VanKampen/SurgeryRegionPairThickening.lean`: `IsRegionPairDart`, `regionPairCount`,
  `regions_of_noRegionPairDart`, `RegionPairThickeningStatement` / `regionPairThickening`
- `GroupApproximation/GGT/VanKampen/SurgeryRegionPairThickeningModel.lean`: a `decide` model test of the doubling
- `GroupApproximation/GGT/VanKampen/SurgeryFaceEdgeDoublingHoldingRegion.lean`: transport of a region holding the doubled
  face along a side dart whose reverse lies outside it, through `FaceEdgeDoubling.dartImage`

Crux: an edge between faces of two selected regions lies on a side of each, since arc darts cross into cells or the
exterior. A doubling separates them only if the digon lies in neither region, so the region holding the doubled face
changes. Its face goes to `cellFace` and the side dart `w_j` to the new dart. No landed transport covers a region
holding `f`: `FaceEdgeDoubling.regionFamily`, `regionFamilyOfArcs` and `DiscEmbeddingAway` all need `f ∉ s`.

**LANDED ef924c4d2** (probe 0913-182150-4009 GREEN, BUILT both; wire-queued):
- `SurgeryRegionPairThickening`: `RegionPairThickening.IsRegionPairDart Delta family x` holds for a dart of a face with at
  least 2 darts in a region `a` whose reverse lies in a region `b ≠ a`. Also `regionPairCount`,
  `regionPairCount_eq_zero_iff`, and `regions_of_noRegionPairDart hno hx hy hxy hmono`, which gives the field `regions`
  for every pair `x ≠ y`. `hmono`, the monogon case, is an explicit hypothesis for now.
- `SurgeryRegionPairThickeningModel` (decide): after doubling the shared edge inside `A` no pair dart remains; `A`'s
  boundary `{0, 3}` becomes `{3, 6}`, i.e. `0 ↦` the new dart; `B`'s boundary is unchanged. Calibration: counting the digon
  inside `A` keeps both pair darts.

Agreements with w1-binder-5 (18:3x):
- It withdraws its side–side claim and consumes `regionPairThickening` for `CellPocketWalk.CopyClean.regions`.
- The statement also keeps, when given, no `CellEdgeThickening.IsCellEdgeDart` and no
  `CellSideThickening.IsCellSideDart`.
- The induction carries an invariant, `exists_regionPairFree_of_invariant (P) (hP) (S) (hS)`, over a named one-step
  family on `FaceEdgeDoubling.diagram` with `target := H.target.map indexEquiv`. This follows the shape of
  `CellSideThickening.exists_cellSideFree_of_invariant`, so `JoinsCells` is carried along.

**LANDED bac6c5722** `SurgeryFaceEdgeDoublingHoldingRegion` (M3 part 1; probe 0913-190359-6379, BUILT/COMPILED; wire-queued):
- `facePerm_dartImage`: face rotation commutes with `dartImage` everywhere, by the two `insertBefore` corners `w_j` and
  `facePerm w_j`.
- `faceOf_dartImage`, `alpha_dartImage_of_ne`, `holdingFaceSet` (images of the faces, without the digon), boundary darts
  `↔` images, internal moves and boundary steps lift, and `holdingBoundary : FaceSetBoundary` with cycle `B.cycle.map
  dartImage`, under `faceOf (α w_j) ∉ s`.

**LANDED 420311fe2** `SurgeryFaceEdgeDoublingHoldingGeometry` (probe 0913-193150-69541, BUILT/COMPILED; wire-queued):
- `shelling_dartImage`, the shelling transport.
- `holdingGeometry`: arcs go through the dart embedding and sides through `dartImage`.
- `holdingCandidate`, with the same weight and target profile.

**LANDED f3a009b81** `SurgeryRegionPairThickeningStep` (probe 0913-194251-26880 GREEN; wire-queued):
- `StepData`: the holder, `w_j` on its side, and the arcs of the other regions avoiding `w_j`.
- `stepFamily`: the holding region inserted into `regionFamilyOfArcs` of the rest, with card, weight, pairwise,
  profile and noLoop.
- `stepEquiv`, with profile, source and `target.map Fin.val`, and `sectionFamily`.

**LANDED 9e31aea90** `SurgeryRegionPairThickeningCount` (probe 0913-195857-98618 GREEN; wire-queued):
- `one_lt_length_or_of_regions` discharges `hmono`. Two monogons across the edge would make the vertex rotation
  swap its darts, so the connected map would have two darts and the exterior would be a region face.
- `side_of_pair`, `familyArcAvoid_of_pair` and `stepDataOfPair`, assuming no relator word has value one.
- `exists_of_isRegionPairDart_step` and `regionPairCount_lt`.

**LANDED 235ce464b** `SurgeryRegionPairThickeningRegions` (probe 0913-203604-50879 GREEN; audit propext, Classical.choice,
Quot.sound, no sorryAx; wire-queued). **`SectionPocketRegionsCopyStatement` is proved**, which closes item 3:
- `noOuterSideDart_step`, `noCellSideDart_step`, `noCellHair_step`, `noCellEdgeDart_step`.
- `exists_regionPairFree_of_invariant (P) (hP) (S) (hvalue) (hS)`. `hP` also receives the relator-value hypothesis, and
  the output adds the target clause and the relator values.
- `RegionsClean` and `sectionPocketRegionsCopy : SectionPocketRegionsCopyStatement`.
- The first probe (20:2x) failed on infra (MSI connection down), not on Lean.

## Item 4 (main, 21:3x): the binder 6 variant and SK LEF part (iv)

CLAIM binder 6 variant `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketFaceSetRegionsProved.lean`:
- `osinSectionPocketFaceSetSection_of_euler` discharges `regions` by `sectionPocketRegionsCopy`, so binder 6 rests only
  on `SectionPocketWalkEulerStatement`.
- It also has `_of_keptCell` variants.
- **LANDED 350fce5b4** (21:39): probe 0913-212739-59611 GREEN, audit with no sorryAx, wire-queued. Additive; attic bcd9ca157.

CLAIM SK LEF part (iv) `GroupApproximation/Manuscript/SimpleKazhdanSofic/LEFDiagonalCommutators.lean`: the diag
identities, `ℓ ↦ diag(u_ℓ,1,1)`, `[L,L] → EL₃(R)`, and `Γ ≤ [Δ,Δ] ≤ [L,L]`. Ledger at `notes/sk-formal/reports/ms-intro-2.md`.
- **LANDED a39853967** (23:5x), at tip c8b6021ca, tex 395–402. Probe 0913-234246-2153 GREEN; wire-queued.
  `printedLEFDiagonalIdentities` and `printedLEFDiagonalEmbedding` hold over any ring with `u : Λ →* Rˣ`.

## Item 5 (main, 00:0x 09-14): piece 2 of ms-compress-1's LongTransitions split (51687cf4b)

CLAIM `OsinLemma94CuttingTransitionInput` (cutting transitions ≤ K n), in new modules
`GroupApproximation/GGT/VanKampen/Estimating/OsinLemma94CuttingTransitions*.lean`. ms-compress-1 keeps piece 1,
`OsinLemma94ContactTransitionInput`.
- Route (the Prop's docstring): a dart-minimal family has no pendant cutting tree, so an entry into a cutting path marks
  a hole of the polygon that holds an object. The entries are bounded by the holes, and the holes by n.
- Model test first: a polygon around one cell joined to `∂Δ` by one bridge gives 2 cutting transitions and 1 hole.
- CLAIM landed 318cd7abe. Split and tooling agreed with ms-compress-1 in one message (00:1x).
- Formal route, K = 4:
  1. Transitions ≤ `sameFaceStarts`.
  2. starts ≤ 2(e − v₀) on X, the same-face darts of unselected G-faces, using `σ x ≠ x` from `DartMinimal`.
  3. The first-return deletion M′ of X has V′ = V − v₀, E′ = E − e and F′ ≥ F, so χ(M′) ≥ 2 + e − v₀.
  4. χ(M′) ≤ 2|T| for a component hitting set T: one dart per relator cell plus one outer dart. So e − v₀ ≤ 2n.
- Planned modules:
  - general: `CombMapEulerHittingSet` and `CombMapFirstReturnCounts`;
  - `Estimating/OsinLemma94CuttingTransitions*`: starts, hitting set and assembly, plus a decide model. Calibration: a
    pendant edge breaks step 2.
- 00:3x–08:2x: MSI master down, then the laptop reboot wiped /private/tmp. All green records were lost. Infra was rebuilt
  at 08:4x and the overlay files were re-added.
- Drafts (attic e79f01b79), probing:
  - `CombMapEulerHittingSet`: `eulerCharacteristic_le_two_mul_card_of_hitting`.
  - `CombMapFirstReturnCounts`: `PredicateRestriction.vertexCount_le`, `dartCount_add`, `faceCount_le`,
    `two_mul_eulerCharacteristic_le`, and `CombMap.card_starts_add_two_mul_le`.
  - `CombMapFirstReturnCountsModel`: the calibration on one edge fixed by the rotation (4 > 2).
  - `Estimating/OsinLemma94CuttingTransitions`: `card_cuttingTransitions_le_sameFaceStarts`, `forestDarts`,
    `sigma_ne_of_mem_forestDarts`, `exists_keep_faceOf_eq`, `forestDeleted`, `card_forestStarts_add_four_le`.
  - `Estimating/OsinLemma94CuttingTransitionsInput`: `Joined`, `exists_joined_cell_of_region` (boundary cycle to the
    source arc, or a closure contradiction), `exists_joined_cellOrOuter`, `hittingSet` (card ≤ n + 1),
    `sum_card_sameFaceStarts_le`, and `osinLemma94CuttingTransitionInput` (K = 4).
- Probe 0914-083104: a stale base (BadJunctionExclusion landed at 08:40), two `rw` pattern misses, one unknown name and a
  `push_neg` lint. All fixed.
- **LANDED 496779d1f** `CombMapEulerHittingSet` (probe 0914-084203-62907 BUILT; audit clean; wire-queued).
- **LANDED ca2bb2fce** `CombMapFirstReturnCounts` (probe 0914-084627-6800 BUILT; audit clean; wire-queued).
- **LANDED ebb6f5faa** `Estimating/OsinLemma94CuttingTransitions` + `CombMapFirstReturnCountsModel` (probe
  0914-085318-62936 BUILT both; audit clean; wire-queued).
- **LANDED 59a5e1718** `Estimating/OsinLemma94CuttingTransitionsInput` (probe 0914-090436-62166 GREEN;
  `#audit_closed_axioms` propext, Classical.choice, Quot.sound; no sorryAx; wire-queued).
  **`OsinLemma94CuttingTransitionInput` is proved** (`osinLemma94CuttingTransitionInput`, K = 4, ε₀ = 0, ρ₀ = 1), which closes
  item 5. The contact piece stays with ms-compress-1.

## Item 6 (main, 09:2x 09-14): help ms-compress-1 close `OsinLemma94ContactTransitionInput`

~~CLAIM building H~~ WITHDRAWN (09:3x): ms-compress-1 had already written H, as `Estimating/OsinLemma94ContactMap`. By
agreement (their reply, 09:3x) I take the small faces instead.

CLAIM `OsinLemma94ContactMapSmallFacesInput` (under the binders of `OsinLemma94LongTransitionInput`, the faces of
`P.contactMap` of degree < 6 number ≤ K·n), in new modules `Estimating/OsinLemma94ContactMapSmallFaces*.lean`.
- ms-compress-1 states the Prop with H, and keeps the counts and the assembly.
- The route, per face (every face has degree ≥ 4, so small faces have degree 4):
  - the face holds a relator cell, which gives at most n such faces;
  - otherwise it is an empty two-gon, excluded by a region merge, `pinchSplitAbsorption`, or ContactBubble.
- Decomposition (09:4x), for a degree-4 face (x, φx, φ²x, φ³x) of `contactMap` through a representative dart x at a
  polygon:
  1. **Degenerate faces.** In a simple bipartite map whose polygon side has degree ≥ 2, v(φx) ≠ v(φ³x) always, and
     v(x) = v(φ²x) forces σ(αx) = αx, a pendant object. Each pendant object dart lies on one face, so there are at most
     n + 1 degenerate faces. This part is pure CombMap and comes first.
  2. **Nondegenerate faces holding a cell or the exterior in their face class** (`CombMapRestrictionFaceClasses`).
     Distinct faces hold disjoint objects, so there are at most n + 1.
  3. **Empty nondegenerate faces**: the residual.
- Risk in part 3. The existing merges collapse whole G-faces:
  - `false_of_avoided_singleton` (0 absorbed regions);
  - `false_of_collapse_singleton` and `false_of_disc_collapse_singleton` (≥ 2 absorbed).

  An empty two-gon is bounded by sectors of the polygon faces f and f′. When d_f = d_f′ = 2 with single a- and b-blocks
  and one region between them, f ∪ region ∪ f′ is a heavier contiguity region, since its sides are the neighbouring
  regions' short sides. For d_f ≥ 3, or a block with several short sides in a row, the merge needs a sector surgery or a
  different argument; nothing on main does that yet. Part 3 gets its own named Prop and a model test before it is built.
- 10:0x resume after the API/DNS outage. Reconciled: every landing through b3c563424 is on origin and in landed.log;
  nothing was half-landed. Probe 0914-093234-44610 died on the MSI hop (infra), with no evidence.
- Drafts (probe 0914-10:0x running):
  - `CombMapBipartiteSmallFaces` (attic 03ecc8ad5): `vertexOf_facePerm_ne_pow_three`, `sigma_alpha_eq_of_vertexOf_eq`,
    `card_filter_degenerate_le`.
  - `Estimating/OsinLemma94ContactMapSmallFaces` (attic 329812ba2): `exists_faceOf_eq_objectFace`,
    `vertexOf_eq_of_faceOf_eq`, `card_fixed_colour_false_le` (≤ n + 1), `card_degenerateFaces_le`, the residual
    `OsinLemma94ContactMapNondegenerateSmallFacesInput`, and `osinLemma94ContactMapSmallFacesInput_of_nondegenerate`
    (K + 2). This is a reduction, and the nondegenerate count stays open.
- **LANDED 8677b0dcd** `CombMapBipartiteSmallFaces` + `Estimating/OsinLemma94ContactMapSmallFaces` (probe
  0914-100802-40974 GREEN, BUILT both; 5 audit lines clean, no sorryAx; wire-queued).
  - Degenerate small faces are at most n + 1.
  - `osinLemma94ContactMapSmallFacesInput_of_nondegenerate` is a reduction with constant K + 2.
  - **Open:** `OsinLemma94ContactMapNondegenerateSmallFacesInput`.
- Scope of the residual (10:2x). Two parts are substantial new geometry.
  1. **Faces holding an object.** `contactMap` can be disconnected, and `IsRestriction.faceOf_eq_of_faceClass` separates
     faces only within a connected component (C5 of Φ′_M works on one linked component). Faces of different components
     can hold the same object, so charging to objects needs the nesting of components: charge each object, or nested
     component, to its innermost face. Nothing on main provides that.
  2. **Empty nondegenerate two-gons.** The pocket is bounded by sectors of polygon faces and object arcs, while
     `EmptyTwoGonInput` (Φ′_M) needs region sides. The sector merge is new.
- Reuse plan for the nondegenerate residual (10:1x), modelled on the proved count for Lemma 9.7(a), Φ′_M:
  - `OsinAppendixEulerSmallFaces` splits small faces into C4 corners, C5 faces holding a cell, and C6′ two-gons holding
    a cell or with a corner.
  - C5: `CellFaceCountInput`, proved in `OsinAppendixEulerExteriorCellFaces`.
    - `HoldsCellO` is defined by `FaceClassStep` in the dual of the collapsed map.
    - `eq_of_holdsCellAtO` shows distinct faces hold distinct cells, by `IsRestriction.faceOf_eq_of_faceClass` on a
      connected linked component.
  - C6: `EmptyTwoGonInput`, proved in `OsinPocketDiscEmptyTwoGon`. It merges two regions of one cell to one section
    through a `PocketRegion` holding no relator cell.
  - For the contact map, the analogues are:
    - `HoldsCell` by `FaceClassStep` in `S.diagram.toCombMap.dual` with `ContactKeep`, per component of `contactMap`
      (`CombMapComponents`);
    - an empty-two-gon Prop for (f, a, f′, b). Its pocket is bounded by polygon sectors and object arcs, not region sides,
      so the merge is new work.
- The earlier H outline, kept for reference:
- H = `PredicateRestriction.toCombMap (S.diagram.toCombMap.dual)`, keeping one dart pair per (polygon f with d_f ≥ 2,
  object o), where o is a relator cell or the exterior.
- Outputs:
  - `IsRestriction` of the planar dual;
  - the colour, simplicity and degree hypotheses of `four_le_faceDegree_of_bipartite`;
  - the counts E(H) = Σ d_f and V(H) ≤ #polygons + n + 1;
  - degree-4 faces as (f, a, f′, b) two-gon data.

## Progress log
- 16:55 ledger landed (2185fb750); module claimed.
- 17:06 probe 0913-170556-76424 GREEN, BUILT IntroCompressorSentences.
- LANDED ef4e63c90 `GroupApproximation/Manuscript/NonMFSentences/IntroCompressorSentences.lean`, queued for wiring:
  - `PrintedIntroCriterionKillsMFImages` / `manuscriptSentence_introCriterionKillsMFImages` (270c3118af88)
  - `PrintedAscendingHNNStableLetterCompressor` / `manuscriptSentence_ascendingHNNStableLetterCompressor` (9bab404c96c5)
  - `PrintedIntroPairGivesCompressor` / `manuscriptSentence_introPairGivesCompressor` (6b5d4b5c3081)
  - `PrintedIntroUniversalGroupMapsEveryEL` / `manuscriptSentence_introUniversalGroupMapsEveryEL` (29d7a8ccf93a)
- Census rows for all six defects: `metadata/nm-census-rows/ms-intro-2.tsv`.
- Range status: after the census merge and wiring, every sentence of tex 166–232 is carried by a closed declaration at the
  printed generality or honestly classified. No residual Props.
