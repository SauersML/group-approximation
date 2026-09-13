# Lane fff-periodic — report

Non-MF verbatim formalization swarm, 2026-09-12.  Clone nm-c.

## 09-13: SharedEdge same-cell case (site 5), ruling (a); binder and word half LANDED unverified

Assignment (lead): patch 03 of ghw-charp2's LoopCut landing adds `hi : i₂ ≠ i` to
`false_of_digon_toward_cell` (`Estimating/OsinUnboundSharedEdge.lean:377`, hull-unbound).  Close the
case it leaves open in a new module: an unbound dart `d` of cell `i` with `α d` on cell `i`.  Either
contradict optimality or least area, or count such darts by something already bounded.

Ruling (lead): option (a).  `Covers` takes a factor `⌈1/λ⌉` on the sides, and `L` may depend on `λ`
and `c`.  This lane proves (T) in a new module.  (C) is a named binder owned by this lane.  It is
stated with the Lemma 9.7 induction hypothesis on smaller diagrams in scope (theoremc-retire's
option (i)).  The `Covers` respelling lands in one co-probe with hull-count94, after ghw-charp2's
(A) co-probe.  Options (b) and (c) are rejected.

Status: LANDED 593ba10c2 with NM_UNVERIFIED, no probe.  The hold continues: `OsinUnboundSharedEdge`
is still at 8009a06ff, so patches 01-10 are not landed.
- `Estimating/OsinUnboundSameCellPocket.lean`: `AvoidEdgeStep` and the (C) binder
  `OsinLemma94SameCellPocketInput`.
- `Estimating/OsinUnboundSameCell.lean`: `stretch_le_length`, `keptLetters`,
  `stretch_le_keptLetters` and the endpoint `OsinUnboundSameCellStretchBound`.

Earlier findings:

1. No competitor under (A).  Same-cell darts lie on no region: `boundary_decomposition` puts both
   arcs on the region's boundary cycle, which runs along its G-faces.  So these darts are always
   unbound.  The doubled digon touches only cell `i`, so its region is a loop.  `nondegenerate`
   forbids empty arcs, and `FaceSetBoundary` has one cycle, so the digon cannot join another region
   at a vertex.
2. `DartMinimal` does not exclude them.  Fold an unbound spur `x x⁻¹` of cell `i` that faces an
   unselected G-face into a pendant edge inside the cell.  The result is O-equivalent, since
   `OEquivalentDiscDiagram` asks only for the boundary word and the cell words.  Weight, card and
   `unboundSum` stay the same, and two darts go away.  This is the cell-side mirror of jacobson's
   `PendantPathRemovalInput`.  So option (v2) of ghw-charp2's patch 10(d) cannot come from
   `DartMinimal`.
3. After the fold these darts are on no polygon walk (`cell_arc`: `sideDarts = arc.reverseDarts`,
   which are walk darts).  `Covers` has to absorb them in `L n`.

A same-cell edge is a bridge.  The component `C2` behind it sits inside cell `i`, whose word reads
`u x p x⁻¹`.

* (T) `C2` has no relator cell, so `x p x⁻¹` has value 1.  Take a maximal unbound stretch with `X`
  same-cell darts and `N` others.  Quasi-geodesicity gives `λ X ≤ (1 − λ) N + c`, and summing gives
  `Σ X ≤ (1/λ − 1)(Σ sides + 24 ε n) + (c/λ)(n + 2|M|)`.  This needs a factor on the sides in
  `Covers`; a larger `L` alone does not suffice.
* (C) `C2` contains relator cells.  The bridge path gives `2|x|` unbound darts with no length bound.
  The value of `x p x⁻¹` need not be 1, and pieces give only `|x| < μ |r|`.  Excluding (C) takes
  Greendlinger on `C2` plus small pieces (Lyndon–Schupp's simple-contour argument), so it needs
  induction on area.

Options sent to the lead:
- (a) Respell `Covers` with a factor `⌈1/λ⌉` on the sides and `L` depending on `λ, c`.  This lane
  proves (T) in a new module, and (C) stays a named binder.  The consumer carries over:
  `dense_of_covers` uses `Covers` only through `linarith`, so a factor `M` on the sides gives
  density at `⌊ρ / (4 M²)⌋`, and `unbound_lt_of_pieces` then asks `4 M² ρₘ ≤ ρ`.  The (T) word
  lemma (a stretch `i..j` of a quasi-geodesic word with a same-value admissible respelling `alt`
  has `λ (j − i) − c ≤ |alt|`) is landed in `OsinUnboundSameCell` (593ba10c2, unverified).
- (b) Change PlanarPieces so a cell side may carry value-one same-cell excursions (Osin's 0-refinement).
- (c) Use a `DartMinimal` measure that keeps spurs unfolded.  The cost is digon polygons, which raise
  `SideBudget`.

audit-sec5 has both configurations for its model test.  A single relator `b^m` inside `r_i` fails
`pieces_small`, as Greendlinger on `C2` predicts.

Sent: the inline (C) binder form to theoremc-retire, for its threading co-probe to pass `hbelow` to
the `Covers` call site.  The respelling plan to hull-count94: `M = ⌈1/λ⌉₊`, density `⌊ρ/(4M²)⌋`,
`L = 24 ε M + 25 ⌈c/λ⌉₊`, `ρ₀ = max(⌈c/λ⌉₊ + 2, ρ_C)`, and the theorem taking
`hpocket : OsinLemma94SameCellPocketInput`.  The ΣX configurations to audit-sec5.

Residual Prop owned: `OsinLemma94SameCellPocketInput` (binder (C)).  Planned discharge: a pocket
with relator cells gives `OsinLoopCut.ofPocketRegion` with `s = []`, then `false_of_below` through
`hbelow`.  This needs a noncrossing pocket builder.

Next, in new modules, all unprobed until ghw-charp2 lands:
1. Bridge lemma.  On a planar map with `faceOf a = faceOf (α a)`, no `AvoidEdgeStep` path joins `a`
   to `α a`.  The proof deletes the edge (`EdgeDeletion.euler_balance_of_sameFace`, `V' = V`), so
   `χ' = 4`.  The deleted map stays connected, contradicting `eulerCharacteristic_le_two`.
2. Head and tail classes of the pocket, the orientation from connectivity, and laminarity of
   same-cell pockets on one cell.
3. The count: `Σ_i |unbound same-cell darts| ≤ ⌈1/λ⌉₊ Σ_i |other unbound darts| + ⌈c/λ⌉₊ (n + 2|M|)`.
4. The `Covers` co-probe with hull-count94.

## 09-13: `EmptyTwoGonInput` closed (route A), LANDED and GREEN

Assignment (lead): a closed producer of hull-euler's `EmptyTwoGonInput`
(`Estimating/OsinAppendixEulerEmptyTwoGon`), keyed on `IsDiscRegion`, so that pinched pockets
(no `FaceSetBoundary`, dgo-geometric's `OsinPocketPinchedTwoGonModel`) are covered.

Producer: `GroupApproximation.GGT.VanKampen.emptyTwoGonInput_holds :
EmptyTwoGonInput D lambda c eps W`, for all parameters, with no hypotheses.
`#print axioms` = [propext, Classical.choice, Quot.sound].

Route A, as assigned.
1. Collapse the pocket interior. `Surgery.InnerDiscRegion` is the inner-collapse structure keyed
   on `region : IsDiscRegion`. `InnerDiscRegion.ofPocketRegion P hcells` builds it from the
   pocket, using `P.inner`.
2. Take the value from `P.listVal_inner_eq_one hcells`.
3. The merged face has no internal dart, so `ContiguityGeometry.ofSingletonFace` gives one
   region (`InnerDiscRegion.mergedGeometry`) whose weight is at least `a.w + b.w`.
4. Transport the other regions with `InnerDiscRegion.regionFamily_profile` and
   `regionFamily_avoid_merged`. The family then has one fewer region and weight at least as
   large, which contradicts `weight_maximal` or `card_minimal`
   (`GloballyDistinguishedSectionFamily.false_of_disc_collapse_singleton`).

The proof does not use `LeastArea`, `a.1 ⊆ P.faces` or `b.1 ⊆ P.faces`. The merged region
targets a section, so the proof stays loop-free under the pending LoopCut ruling.

| Module | Lines | Landed |
|---|---|---|
| `V/SurgeryInnerDiscCollapse` | 250 | da2d0b963 |
| `V/SurgeryInnerDiscCollapseDarts` | 369 | da2d0b963 |
| `V/SurgeryInnerDiscCollapseRegions` | 370 | da2d0b963 |
| `V/SurgeryInnerDiscCollapseMerged` | 77 | da2d0b963 |
| `V/Estimating/OsinPocketDiscMerge` | 257 | 2aa17abb0 |
| `V/Estimating/OsinPocketDiscEmptyTwoGon` | 89 | 2aa17abb0 |

The four collapse modules copy `SurgeryInnerCollapse*` with the region keyed on `IsDiscRegion`
(`InnerGRegion` → `InnerDiscRegion`, `R.boundary.cycle` → `R.region.cycle`).
`SurgeryGCellCollapse.InteriorGCellRegion` has no transport API, so these modules do not
duplicate it.

Verification.
- Probe `0913-091627-32913` (base fd51edbc6, which contains the CutMerge omega fix e7e55c0f2):
  PROBE GREEN. It BUILT `OsinPocketDiscMerge` and `OsinPocketDiscEmptyTwoGon`, with no errors
  and no warnings.
- The four collapse modules were BUILT in probe `0913-090831-85897` on the same bytes. In the
  later probe they were replayed and COMPILED.
- The bytes of all six files equal origin/main.
- The six modules are queued in `wire-queue.txt`.
- An earlier probe went red only at the peer's `OsinAppendixCutMerge:103`. hl-lemma46 fixed it
  at e7e55c0f2, and I did not edit that file.

Residual Props: none. No census row is added, because `EmptyTwoGonInput` is hull-euler's piece
Prop. The signatures of `Systolic.mirrorFold` and `mirrorFoldPinched` are unchanged.

## 09-13: four-leaf endpoint flips, LANDED and GREEN

Assignment (lead, after hfold closed): every baseline declaration of `TorsionFreeFourLeaves`,
`TorsionFreeSectionSentencesFourLeaves` and the other four-wall consumers outside the hull-bridge
and ghw-assembly sets gets one `_of_greendlinger` form.  Each form uses all three closed
producers, so only `hgreendlinger` stays a binder.

Module `Manuscript/NonMF/TorsionFreeGreendlingerLeaf`, namespace
`GroupApproximation.Manuscript.NonMF.TorsionFreeGreendlingerLeaf`.  LANDED 1edf0f7b4.  Probe
0913-063820-983 (base efb80f4fd): `PROBE GREEN`, `BUILT` for the module.  The normal landing after
it reports `NOTHING TO LAND` (bytes = origin/main 4caf6aea2).  It is in `wire-queue.txt` at 1edf0f7b4.

Each theorem is `(hgreendlinger :
GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) : <conclusion>`.  Its
body is the matching `_of_fourLeaves` theorem, applied to these producers:

* hbridge: `HullSC.relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed` (18682110d);
* hKO: `KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed` (ko-closed, f65f99f17);
* hW: `HydeLodha.finitelyPresentedInfiniteSimple_closed`.

| `_of_greendlinger` form | conclusion | producers used |
|---|---|---|
| `printedHullTheorem` | `TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0}` | hbridge |
| `printedHullTheoremOsin` | `TorsionFreeOsinNotion.PrintedHullSmallCancellationOsin` | hbridge |
| `printedHullTheoremLimitSet` | `TorsionFreeLimitSetNotion.PrintedHullSmallCancellationLimitSet` | hbridge |
| `hullSmallCancellationTorsionFreePrinted` | `TorsionFreePrinted.HullSmallCancellationTorsionFreePrinted.{0}` | hbridge |
| `printedSaturation` | `TorsionFreePrinted.PrintedSaturationNoOmega.{0}` | hbridge |
| `printedSaturationOsin` | `TorsionFreeOsinNotion.PrintedSaturationOsin` | hbridge |
| `printedSaturationLimitSet` | `TorsionFreeLimitSetNotion.PrintedSaturationLimitSet` | hbridge |
| `hullCommonQuotient` | `TheoremC.HullCommonQuotientStatement` | hbridge |
| `fournierFacioQuotient` | `TheoremC.FournierFacioQuotientStatement` | hbridge |
| `literatureInputs` | `TheoremC.LiteratureInputs` | hbridge, hKO |
| `configuration` | `Nonempty TheoremC.Configuration` | hbridge, hKO |
| `fournierFacioParagraph` | `TorsionFreePrinted.FournierFacioParagraph` | hbridge, hKO, hW |
| `printedTorsionFreeTheorem` | `TorsionFreePrinted.PrintedTorsionFreeTheorem` | hbridge, hKO, hW |
| `printedTorsionFreeFullMFRadical` | `TheoremC.PrintedTorsionFreeFullMFRadical` | hbridge, hKO, hW |
| `printedTorsionFreeTheoremOsin` | `TorsionFreeOsinNotion.PrintedTorsionFreeTheoremOsin` | hbridge, hKO, hW |
| `printedTorsionFreeTheoremLimitSet` | `TorsionFreeLimitSetNotion.PrintedTorsionFreeTheoremLimitSet` | hbridge, hKO, hW |
| `printedRegularNonMFAlgebra` | `TorsionFreePrinted.PrintedRegularNonMFAlgebra` | hbridge, hKO, hW |
| `printedRegularNonMFAlgebraOsin` | `TorsionFreeOsinNotion.PrintedRegularNonMFAlgebraOsin` | hbridge, hKO, hW |
| `printedRegularNonMFAlgebraLimitSet` | `TorsionFreeLimitSetNotion.PrintedRegularNonMFAlgebraLimitSet` | hbridge, hKO, hW |
| `printedHullProofParagraph` | `TorsionFreeSectionSentencesFourLeaves.PrintedHullProofParagraph` | hbridge |
| `printedSaturationPairAndHullAgain` | `TorsionFreeSectionSentencesFourLeaves.PrintedSaturationPairAndHullAgain` | hbridge |
| `printedSaturationApplyHull` | `TorsionFreeSectionSentencesFourLeaves.PrintedSaturationApplyHull` | hbridge |
| `printedTheoremApplySaturation` | `TorsionFreeSectionSentencesFourLeaves.PrintedTheoremApplySaturation` | hbridge |

`TheoremC.manuscriptTorsionFree*`: theoremc-retire already has the flips,
`TheoremC.manuscriptTorsionFreeFullMFRadical_of_greendlinger` and
`TheoremC.manuscriptTorsionFreeSimplified_of_greendlinger`
(`TheoremCAssemblyGreendlingerLeaf`, c5f953323, green 0913-060950-64731).  Those names are not
duplicated here.

Final flip ownership (roster, ~06:30): this lane has `TorsionFreeFourLeaves` (38 findings) and
`TorsionFreeSectionSentencesFourLeaves` (12 findings).  The TheoremC names go to theoremc-retire.
`TorsionFreeSectionAssembly` (the closedGO forms and `manuscriptRegularNonMFAlgebra_closedCitations`)
goes to hull-bridge, whose unlanded `TorsionFreeGreendlingerForms` covers it.  So the census rows
retire only the `_of_fourLeaves` findings of these two modules.

Residual Prop: `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}` only
(the Hull 7.1 chain).  Once it has a closed producer, each endpoint above is closed by applying it.

Census: rows at the keys of these endpoints are in `rows/fff-periodic.tsv`, corrected to this
ownership at 84cf2efbb.  They retire the 46 open-predicate and buried-conditional findings of the
23 `_of_fourLeaves` theorems.  They do not retire the 4 carrier-data findings on the sentence Props
`PrintedHullProofParagraph`, `PrintedSaturationPairAndHullAgain`, `PrintedSaturationApplyHull` and
`PrintedTheoremApplySaturation`, because those defs are unchanged.  The census lane has the old → new
names for each retired line.

hull-bridge's `TorsionFreeGreendlingerSentences` (2aa98f8cc) covers the tex sentences at lines 1662,
1665, 1698 and 1680 too.  It uses the `_of_leastAreaLeaves` producers with their own Props, and this
module uses the `_of_fourLeaves` producers.  Neither module repeats a name from the other.

## 09-13: hfold (HC6, the mirror fold), CLOSED

Non-MF every-line swarm, 2026-09-13.  Clone spare1.  Target: the closed hfold,
`Systolic.MirrorFoldStatement CCKW.cosetComplex`, stated for every triangle complex.

Closed endpoints, namespace `GroupApproximation.Systolic`, module `GGT/SystolicDiscMirrorFold`:

* `theorem mirrorFoldPinched {V : Type u} (X : TriangleComplex V) : MirrorFoldPinchedStatement X`
* `theorem mirrorFold {V : Type u} (X : TriangleComplex V) : MirrorFoldStatement X :=
  mirrorFoldStatement_of_cases (mirrorFoldDistinct X) (mirrorFoldPinched X)`

The distinct case `mirrorFoldDistinct` is ko-closed's (`GGT/SystolicDiscMirrorFoldDistinct`, 81b06b43e).
`#audit_axioms` on `mirrorFold`, `mirrorFoldPinched`, `FoldStage.exists_disc_of_pinch` and
`FoldStage.exists_disc_of_sides`: `[propext, Classical.choice, Quot.sound]`.

| module | last landing | evidence |
|---|---|---|
| `GGT/SystolicDiscMirrorFoldStage` | c88b8c1db | COMPILED in 0913-052528-4751 |
| `GGT/SystolicDiscMirrorFoldRestrict` | e12190690 | probe 0913-034739-16916, BUILT |
| `GGT/SystolicDiscMirrorFoldPinchedStage` | 08ae1c587 | probe 0913-051405-91655, BUILT |
| `GGT/SystolicDiscMirrorFold` | 426813b24 | probe 0913-052528-4751, BUILT |

All four are in `wire-queue.txt` at these SHAs; Restrict went in wiring wave 4.

Route of the pinched case.  `FoldStage` is a map with vertex labels, an exterior face cycle and a
set of pending darts; off the cycle and the pending darts every face is a triangle of `X`.
`toStage` reads a triangulated disc as a stage with nothing pending.  `IsPinch S δ`: planar,
nothing pending, `δ` and `alpha δ` off the exterior cycle on distinct faces, and the darts two
steps after them at one vertex.  Delete the edge of `δ`: the two triangles merge into the square
`e1 e2 f1 f2`, and `alpha e1`, `alpha f1` sit at one vertex.  Split that vertex between `e1` and
`f1` (`FoldMap.joined`).  The Euler characteristic becomes 4 (`PinchLemma.split_euler`), the face
count is back to that of `S`, and every dart is reached from `e2` or from `e1` but not both
(`reach_or_reach`, `not_reach_p`).  `pinchStage` keeps the boundary, with the square pending.
On the side of the exterior cycle, `e2 f1` or `e1 f2` is a digon.  `exists_disc_of_sides`
restricts to that side (planar), deletes the digon, and reads the result as a triangulated disc
with at least three faces fewer.  So `innerFaceCount + 2 ≤`.

Consumers this discharges (owners told 09-13):

* ko-closed: `KotowskiOllivierClosed.kotowskiOllivier_of_pinched (hpinch)` at `CCKW.cosetComplex`.
* kh-cckw: `CCKW.systolicInvariantClique_of_pinched`, hypothesis `∀ V X, MirrorFoldPinchedStatement X`.
* theoremc-retire: `TheoremCAssemblyFoldLeaf`, hypothesis `∀ V X, MirrorFoldStatement X`.
* `hfold` binders at generic `X`: `SystolicProjection:110/146/187`, `SystolicDiscFilling:149`,
  `SystolicTriangleCondition:66`, `SystolicInvariantClique:100`, `SystolicProjectionClique:138`,
  `GHBHyperbolicFilling:77/104/118`, `GHBHyperbolicDiscCounts:85`, `CCKWSystolicInvariantClique`,
  `TheoremCAssemblyKOLeaves`.

Residual Props owned by this lane: none.  No census row: the manuscript sentence is tex line 1675,
carried by ko-closed's row `LINE:1675`.

Lean traps at this pin:

* `le_of_le_of_eq` is not the general order lemma; use `LE.le.trans_eq`.
* Annotate lambda binders as `(S.delMap δ).Dart`, not `EdgeDeletion.Dart S.map δ`, so the
  classical `DecidableEq` instance agrees inside `Equiv.apply_swap_eq_self`.
* `EdgeDeletion.alpha_val` is stated through `EdgeDeletion.alpha`; bring it to
  `(toCombMap M a).alpha` with a `have … := alpha_val …` by defeq, not `rw`.

## Scope: surgery 3 of Osin's Lemma 9.4, Case 2

Osin (arXiv:math/0411039v3, §9), Lemma 9.4, Case 2 splits a vertex of a disc diagram at a pinch
between two complementary G-faces.  A realized section family whose regions avoid both pinch faces
survives the split with the same weight, the same number of regions, the same unbound darts on
every relator cell, and legal labels.  A distinguished family stays distinguished.  Five modules,
all compiled:

| module | last landing | evidence |
|---|---|---|
| `GGT/VanKampen/SurgeryPinchSplitMap` | 33bae46eb | compiled at base 44c6bab14 (imported by Sections) |
| `GGT/VanKampen/SurgeryPinchSplitDiagram` | 0c40dd430 | compiled at base 44c6bab14 (imported by Sections) |
| `GGT/VanKampen/SurgeryPinchSplitRegions` | a6fb37e10 | probes 0912-092950-86238 and 0912-093903-22668, COMPILED (cache restore) |
| `GGT/VanKampen/SurgeryPinchSplitSections` | 556c54a9c | probe 0912-092950-86238, BUILT; 0912-093903-22668, COMPILED |
| `GGT/VanKampen/SurgeryPinchSplitExtremal` | c48fbb6c7 | probe 0912-093903-22668, BUILT |

Probe 0912-092950-86238: base 44c6bab14, 5010 jobs, `PROBE GREEN`.  Probe 0912-093903-22668: base
c48fbb6c7, 5011 jobs, `PROBE GREEN`; a normal land of Extremal then reports `NOTHING TO LAND`.  Every
audited declaration depends on `[propext, Classical.choice, Quot.sound]` only.  The earlier probe
0912-003931-85645 was red only on the unbound-dart block of Sections; 556c54a9c rewrote it.

Wiring: the lead's next root-wiring wave takes `SurgeryPinchSplitSections` (with Regions) at the green
bytes.  Edits to those two land `NM_ATTIC` until a probe is green, never `NM_UNVERIFIED`.  Extremal is
still an orphan.

## Statements

Namespace `GroupApproximation.GGT.VanKampen.PinchSplit`.  Inside `Input`:
`{Delta : DiscDiagram.{u, w, v} W} [DecidableEq Delta.toCombMap.Dart] (I : Input Delta)
{D : RelGenSet G Lambda} {eps : ℕ}`.

Regions (`SurgeryPinchSplitRegions`):

* `abbrev Input.Avoids (s : Finset Delta.toCombMap.Face) : Prop := I.leftFace ∉ s ∧ I.rightFace ∉ s`
* `noncomputable abbrev Input.faceSet (s : Finset Delta.toCombMap.Face) :
  Finset I.diagram.toCombMap.Face := s.image I.kept`
* `Input.merged_not_mem_faceSet {s} (hs : I.Avoids s) : I.merged ∉ I.faceSet s`
* `Input.faceSet_disjoint_iff (_hs : I.Avoids s) (ht : I.Avoids t) :
  Disjoint (I.faceSet s) (I.faceSet t) ↔ Disjoint s t`
* `Input.faceSet_inj (hs : I.Avoids s) (ht : I.Avoids t) (h : I.faceSet s = I.faceSet t) : s = t`
* `noncomputable def Input.transportBoundary {s} (hs : I.Avoids s) (B : FaceSetBoundary Delta s) :
  FaceSetBoundary I.diagram (I.faceSet s)`, with
  `@[simp] Input.transportBoundary_cycle : (I.transportBoundary hs B).cycle = B.cycle`
* `noncomputable def Input.regionCandidate (a : { a : RegionCandidate D eps Delta // I.Avoids a.1 }) :
  RegionCandidate D eps I.diagram := ⟨I.faceSet a.val.1, I.contiguityGeometry a.property a.val.2⟩`
* `noncomputable def Input.regionFamily (family : Finset (RegionCandidate D eps Delta))
  (havoid : ∀ a ∈ family, I.Avoids a.1) : Finset (RegionCandidate D eps I.diagram)`
* `Input.regionFamily_card : (I.regionFamily family havoid).card = family.card`
* `Input.regionFamily_weight : EstimatingSelection.familyWeight RegionCandidate.weight
  (I.regionFamily family havoid) = EstimatingSelection.familyWeight RegionCandidate.weight family`
* `Input.regionFamily_pairwise (hcompat : EstimatingSelection.PairwiseCompatible
  RegionCandidate.Compatible family) : EstimatingSelection.PairwiseCompatible
  RegionCandidate.Compatible (I.regionFamily family havoid)`
* `Input.regionFamily_faces (ha : a ∈ I.regionFamily family havoid) : ∃ b ∈ family, a.1 = b.1.image I.kept`
* `Input.regionFamily_avoid_merged : ∀ a ∈ I.regionFamily family havoid, I.merged ∉ a.1`

Sections (`SurgeryPinchSplitSections`):

* `Input.regionFamily_profile (ha : a ∈ I.regionFamily family havoid) :
  ∃ b ∈ family, RegionCandidate.SameTargetProfile a b`
* `Input.cellArcDarts_regionCandidate a i :
  (I.regionCandidate a).cellArcDarts (I.cellMap.indexEquiv i) = a.val.cellArcDarts i`
* `Input.boundDarts_regionFamily family havoid interior i :
  RegionCandidate.boundDarts (I.regionFamily family havoid) interior (I.cellMap.indexEquiv i) =
    RegionCandidate.boundDarts family interior i`
* `Input.unboundDarts_eq family havoid i :
  RegionCandidate.unboundDarts (I.regionFamily family havoid) (I.cellMap.indexEquiv i) =
    RegionCandidate.unboundDarts family i`
* `Input.unboundDarts_card`: the card form of `unboundDarts_eq`
* `Input.sum_unboundDarts_card family havoid :
  ∑ j : Fin I.diagram.rCellCount, (RegionCandidate.unboundDarts (I.regionFamily family havoid) j).card =
    ∑ i : Fin Delta.rCellCount, (RegionCandidate.unboundDarts family i).card`
* generic helpers `Input.mem_boundDarts_iff {Xi}`, `Input.mem_unboundDarts_iff {Xi}`,
  `Input.mem_cellArcDarts_iff {Xi}`

Outside `Input`, with `{lambda c : ℝ} {cuts : SectionCuts D lambda c Delta.boundaryWord}`:

* `noncomputable def transportSection (S : RealizedSectionFamily D lambda c eps Delta cuts)
  [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram) (havoid : ∀ b ∈ S.family, I.Avoids b.1) :
  RealizedSectionFamily D lambda c eps Delta cuts`
  (diagram := I.diagram, equiv := S.equiv.trans I.oEquivalent, family := I.regionFamily S.family havoid)
* `transportSection_weight : (transportSection S I havoid).weight = S.weight`
* `transportSection_card : (transportSection S I havoid).family.card = S.family.card`
* `transportSection_labelLegal (E : RelGenSet G Lambda) (h : S.toRealizedRegionFamily.LabelLegal E) :
  (transportSection S I havoid).toRealizedRegionFamily.LabelLegal E`
* `transportSection_diagram : (transportSection S I havoid).diagram = I.diagram` (rfl)
* `transportSection_family : (transportSection S I havoid).family = I.regionFamily S.family havoid` (rfl)

Extremal (`SurgeryPinchSplitExtremal`), with the same outer binders and every declaration taking
`(S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) [DecidableEq S.diagram.toCombMap.Dart]
(I : Input S.diagram) (havoid : ∀ b ∈ S.family, I.Avoids b.1)`:

* `noncomputable def transportDistinguished S I havoid : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts`
  (toRealizedSectionFamily := transportSection S.toRealizedSectionFamily I havoid)
* `transportDistinguished_weight : (transportDistinguished S I havoid).toRealizedSectionFamily.weight =
  S.toRealizedSectionFamily.weight`
* `transportDistinguished_card : (transportDistinguished S I havoid).family.card = S.family.card`
* `transportDistinguished_avoid_merged : ∀ a ∈ (transportDistinguished S I havoid).family, I.merged ∉ a.1`
* `transportDistinguished_toRealizedSectionFamily : (transportDistinguished S I havoid).toRealizedSectionFamily =
  transportSection S.toRealizedSectionFamily I havoid` (rfl)
* `transportDistinguished_diagram : (transportDistinguished S I havoid).diagram = I.diagram` (rfl)
* `transportDistinguished_family : (transportDistinguished S I havoid).family = I.regionFamily S.family havoid` (rfl)

## Why no reverse transport

`GloballyDistinguishedSectionFamily.weight_maximal` and `card_minimal`
(`Estimating/OsinAppendixSections.lean`) compare against every `RealizedSectionFamily D lambda c eps
Delta cuts` with legal labels.  Such a family lives on any reduced diagram O-equivalent to `Delta`,
so the competitors do not depend on which diagram carries the optimum.  The design contract at
lines 89–93 of that file says a surgery that keeps the relator cells and the selected regions yields
another optimum.  `transportSection` keeps the weight, the card and the legal labels, and it stays in
the same class (`equiv := S.equiv.trans I.oEquivalent`).  So `weight_maximal` is
`S.weight_maximal other hother` followed by the weight equation, and `card_minimal` is
`S.card_minimal` read through the card and weight equations.  No map from families on `I.diagram`
back to `Delta` is needed.

## Lean trap

`I.diagram.toCombMap.Dart` is `Delta.toCombMap.Dart` only at default transparency.  A membership
that mixes the two is ill-typed for `rw` and `simp` (instance transparency), and `simp only
[Finset.mem_biUnion]` leaves a `Quot.lift` membership behind.  State membership lemmas at a generic
diagram `{Xi}` and compare across the split in term mode: `Iff.trans`, `and_congr` / `or_congr` /
`not_congr`, `Finset.ext_iff.mp`, and `Iff.of_eq (congrArg (fun l : List I.diagram.toCombMap.Dart =>
d ∈ l) h)`.  `CyclicArc.mapTo_darts _ id _` cannot infer its equation argument; pass it explicitly.

## Residual

* hull-select and dgo-analytic both answered that neither consumes `weight_maximal` or `card_minimal`
  after a pinch split.  hull-select's induction (`Estimating/OsinAppendixSectionInduction`) reads only
  `S.family` and `S.diagram` through five input Props: MultipleEdgeCutInput and LoopCutInput
  (go-lemma42), EulerCountInput (hull-euler), UnboundInput (hull-unbound), DescentInput (dgo-analytic).
  dgo-analytic's pocket induction takes a fresh `exists_globallyDistinguishedSectionFamily` on each
  pocket.  Extremality is used inside the producers: the merge in `SectionPocketCutInput` (hull-respell)
  and the Case 2 argument of UnboundInput (hull-unbound).  On main (grep at 9b29a2730) no landed file
  reads these fields of `GloballyDistinguishedSectionFamily`.  `OsinUnboundCaseOne:36` and
  `UnboundScaledDecomposition:39–40` mention them only in docstrings.  `transportDistinguished` is
  the spelling for any producer that carries S across a split.  Lane handed back for reassignment.
* No census row: these are intermediate carriers in the proof of Lemma 9.4, Case 2, and close no
  manuscript sentence by themselves.
* Spellings sent to hull-select and dgo-analytic (least-area waist) and to the lead.
