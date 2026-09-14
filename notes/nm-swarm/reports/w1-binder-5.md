# w1-binder-5: second start on binder 5 of the W1 waist

Lane of session `nonsofic-existence-49` (wave 2, 2026-09-13). It lands new modules only and never edits owners' files.

## Binder, verified at origin/main 19d96c2c5

- `OsinMultipleEdgePocketRegionSectionStatement` (`Estimating/OsinPocketMultipleEdgeAssembly.lean:195`). With the
  quantifier prefix of `OsinMultipleEdgeCutSectionStatement`, it concludes `MultipleEdgePocketRegionInput`
  (`Estimating/OsinPocketRegionSide.lean:49`) on `S.diagram`, with both `FollowsBoundary` clauses.
- Consumers: `osinMultipleEdgeCutSection_of_pieces`, `OsinDescentResiduals`, `OsinGreendlingerOpenResiduals`.
- Truth status (main's 15:45 ruling, after audit-sec5's truth audit): on `S.diagram`, configuration (b′) has no `P`,
  so the `S.diagram` form is circular. hull-select restates it on an O-equivalent copy with legal labels (drafts r1,
  Rule 22 co-probe).

## Producer route: the cell-to-cell analogue of kh-ejz's section-pocket route

| step | piece | state |
|---|---|---|
| 1 | walk data `s_1 t_1 s_2 t_2` | `CellPocketWalk.exists_of_joinsCells` (jacobson, 65e5e758c) |
| 2 | the walk is a nonempty closed walk (`chain`, `closes`) | no statement on origin, no in-flight file: CLAIMED below |
| 3 | `nodup`, `alpha_not_mem` on a copy | section-pocket analogue: hs-vanishes' `OsinPocketCopyWalk`; cell version open |
| 4 | orientation | section-pocket analogue: cite-hull's `PocketWalkColour.walk_orient` |
| 5 | kept cell | zero-cell merge (hull-select, closed on `S.diagram`) |
| 6 | pocket face set, pinch, region with both `FollowsBoundary` | audit-sec5 owns the cell-to-cell face set and pinch Prop (15:25 ruling) |

## Claims

CLAIM cell pocket walk chain and closes: `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketCellWalkChain.lean`
- `CellPocketWalk.walk_isChain_closes`
- `CellPocketWalk.exists_of_joinsCells_closedWalk`

Both consume kh-ejz's `OsinPocketWalkChain` (ecb23058f) and jacobson's `OsinPocketCellWalk`.

## Landed

- **Step 2 CLOSED: cb5b195c8** (probe 0913-170545-75404 GREEN at base 46dd14831, BUILT
  `OsinPocketCellWalkChain`, empty error index, no `sorryAx`). The module is new, unwired and wire-queued.
  Every declaration is under `#audit_axioms`:
  ```lean
  theorem closedWalk_isChain_closes_of_interleave {S₁ T₁ S₂ T₂ A₁ A₂ B₁ B₂ : List α}
      (hA : (A₁ ++ S₂ ++ A₂).IsChain R) (hB : (B₂ ++ S₁ ++ B₁).IsChain R)
      (hT₁ : T₁.IsChain R) (hT₂ : T₂.IsChain R) (hT₁ne : T₁ ≠ []) (hT₂ne : T₂ ≠ [])
      (hT₁h : T₁.head? = B₁.head?) (hT₁l : T₁.getLast? = A₁.getLast?)
      (hT₂h : T₂.head? = A₂.head?) (hT₂l : T₂.getLast? = B₂.getLast?) :
      (S₁ ++ T₁ ++ S₂ ++ T₂).IsChain R ∧
        ∀ a ∈ (S₁ ++ T₁ ++ S₂ ++ T₂).getLast?, ∀ b ∈ (S₁ ++ T₁ ++ S₂ ++ T₂).head?, R a b
  theorem CellPocketWalk.walk_ne_nil (K : CellPocketWalk D eps X i j) : K.walk ≠ []
  theorem CellPocketWalk.walk_isChain_closes (K) (hij : i ≠ j) (ha : a.JoinsCells i j)
      (hb : b.JoinsCells i j) (hai hbi haj hbj : 0 < (_.cellArcList _).length)
      (hfirst : K.firstSide = b.sideFrom j) (hsecond : K.secondSide = a.sideFrom i) (G₁ G₂)
      (h₁ : K.firstArc.darts = a.cellArcList i ++ G₁ ++ b.cellArcList i)
      (h₂ : K.secondArc.darts = b.cellArcList j ++ G₂ ++ a.cellArcList j) :
      K.walk.IsChain R ∧ ∀ x ∈ K.walk.getLast?, ∀ y ∈ K.walk.head?, R x y
  theorem CellPocketWalk.exists_of_joinsCells_closedWalk (S : RealizedSectionFamily …)
      (ha hb hab) (hij : i ≠ j) (hai hbi) :
      ∃ K, (the conjuncts of exists_of_joinsCells) ∧
        ∃ hne : K.walk ≠ [], K.walk.IsChain R ∧ R (K.walk.getLast hne) (K.walk.head hne)
  ```
  Here `R d e` is `vertexOf (alpha d) = vertexOf e`. The joints `t_2 s_1` and `s_1 t_1` come from `b`'s boundary cycle
  rotated by `(invDarts (b.cellArcList i) ++ b.sideFrom i).length`. The joints `t_1 s_2` and `s_2 t_2` come from `a`'s
  boundary cycle (`boundary_cycle_rotate_of_joinsCells`).
- No census rows: the module certifies no printed sentence on its own.

## Step 3: cell edge conditions, LANDED e9d8d2faf

Probe 0913-173309-80479 GREEN at base bb32c57f9: BUILT `OsinPocketCellCopyWalk`, empty error index, no `sorryAx`. The
module is unwired and wire-queued.

Split agreed with ms-intro-2 (17:2x):
- ms-intro-2 takes step 4, the orientation (`OsinPocketCellWalkColour`), then step 5, the kept cell.
- This lane keeps step 3.
- Step 6 waits for audit-sec5's cell-to-cell face set and pinch statement.

Module `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketCellCopyWalk.lean`, new. Attic copy 617304ab9.

```lean
structure CellPocketWalk.CopyClean (a b : RegionCandidate D eps X) (i j : Fin X.rCellCount) : Prop where
  cell_self_first  : ∀ d, faceOf d = (cell X i).face → faceOf (alpha d) ≠ (cell X i).face
  cell_self_second : ∀ d, faceOf d = (cell X j).face → faceOf (alpha d) ≠ (cell X j).face
  cell_cell        : ∀ d, faceOf d = (cell X j).face → faceOf (alpha d) ≠ (cell X i).face
  regions          : ∀ d, faceOf d ∈ a.1 → faceOf (alpha d) ∉ b.1
  side_first       : ∀ d ∈ b.sideFrom j ++ a.sideFrom i, faceOf (alpha d) ≠ (cell X i).face
  side_second      : ∀ d ∈ b.sideFrom j ++ a.sideFrom i, faceOf (alpha d) ≠ (cell X j).face
theorem CellPocketWalk.walk_nodup_and_alpha_not_mem (hlea : X.LeastArea) (K : CellPocketWalk D eps X i j)
    (hij : i ≠ j) (hfirst : K.firstSide = b.sideFrom j) (hsecond : K.secondSide = a.sideFrom i)
    (hab : Disjoint a.1 b.1) (hclean : CopyClean a b i j) :
    K.walk.Nodup ∧ ∀ d ∈ K.walk, X.toCombMap.alpha d ∉ K.walk
theorem CellPocketWalk.exists_of_joinsCells_clean (S : RealizedSectionFamily …) (ha hb hab hij hai hbi) :
    ∃ K, (the data of exists_of_joinsCells) ∧ ∃ hne, chain ∧ closes ∧
      (S.diagram.LeastArea → CopyClean a b i j → K.walk.Nodup ∧ alpha_not_mem)
def CellPocketCopyCleanStatement : Prop   -- stated, not proved: a globally distinguished family over
  -- a least-area Δ with a ≠ b joining i ≠ j has a globally distinguished family S' over the same Δ and
  -- cuts with a' ≠ b' in S'.family joining i' ≠ j' and CopyClean a' b' i' j'
theorem CellPocketWalk.exists_clean_of_copy (hcopy : CellPocketCopyCleanStatement) (hlea) (S) (ha hb hab hij hai hbi) :
    ∃ S' a' b' i' j' K, membership ∧ joins ∧ CopyClean ∧ walk data ∧ chain ∧ closes ∧ Nodup ∧ alpha_not_mem
```

- Clause usage, from the 16 dart-pair cases:
  - The six clauses are exactly what `alpha_not_mem` needs.
  - Nodup across the two arcs uses `Embedded.cell_face_ne hij`, not a clause.
  - No outer-face clause is needed.
- `CellPocketCopyCleanStatement` is not model-tested:
  - It does not tie `S'` to `S`, which is enough because the multiple-edge cut concludes on `Δ` itself.
  - Expected producer: edge doubling along the offending edges (cell self-edges, Π_i–Π_j edges, a–b edges, sides along a cell), with weight and card unchanged, as in `OuterSpurThickeningStatement`.

## Producer (i) for `CellPocketCopyCleanStatement` (main's 17:5x assignment)

Truth analysis, dart by dart. No falsity found; the risk is construction. Three surgeries:

| surgery | clauses | doubling | region transport | owner |
|---|---|---|---|---|
| T1 cell edges | `cell_self_first`, `cell_self_second`, `cell_cell` | inside the relator face of the dart (`FaceEdgeDoubling.diagram`) | regions avoid both relator faces when no relator word has value one: existing `FaceEdgeDoublingRegions.regionFamily` | this lane |
| T2 cell–side | `side_first`, `side_second` | inside the relator face | the region on the other side contains the across face | ms-cite-2 (`SurgeryCellSideThickening`, in flight) |
| T3 side–side between two regions | `regions` | inside a region G-face | region containing the doubled face, boundary dart replaced: no transport on main | unowned |

- Configuration (b′) and same-cell spurs are T1: an edge with `Π_i` on both sides. Its darts lie on no contiguity arc,
  since an arc dart has a region face across it.
- T1 counts only relator faces with at least two darts. Two distinct regions with nondegenerate disjoint arcs on `Π_i`
  force two distinct darts of `Π_i`, so the clauses at `Π_i` and `Π_j` still follow.

CLAIM T1 cell-edge thickening: `GroupApproximation/GGT/VanKampen/SurgeryCellEdgeThickening.lean`, plus its model
`GroupApproximation/GGT/VanKampen/SurgeryCellEdgeThickeningModel.lean`, in the precedent style of
ms-cite-2's `SurgeryCellSideThickeningModel`: `decide` on dart permutations before and after doubling, for a spur on a
relator face and for a relator–relator edge.

### T1 LANDED 70c183593 (probe 0913-181626-55683 GREEN: BUILT both modules, empty error index, no `sorryAx`; wire-queued)

### T1 status (18:2x)

- `SurgeryCellEdgeThickening` (closed endpoint `cellEdgeThickening : CellEdgeThickeningStatement`) compiled in probe
  0913-180952-14318. The model test failed there only on `norm_num` in `Fin.castLE` bounds, fixed with `decide`.
- The re-probe covers the fixed model and T1. T1 now consumes the collar-double face lemmas
  (`FaceEdgeDoubling.faceOf_none_digon`, `faceOf_embed_dart_digon`, `faceOf_embed_of_face_of_ne`,
  `faceOf_embed_of_face_ne`) in place of three duplicate map-level lemmas.
- Attic copies: e4f23d8a6, d366721fb, 3d263dca3.
- `exists_of_isCellEdgeDart` holds for the doubling along any dart of any inner face, so later doublings (T2, T3)
  keep the absence of cell-edge darts.

### Overlaps and assembly (18:3x)

- **T3 claim WITHDRAWN.** ms-intro-2 claimed the same piece at 18:30 for binder 6: `SurgeryRegionPairThickening`, plus
  `SurgeryFaceEdgeDoublingHoldingRegion`, the transport of a region holding the doubled face. main asked for one
  transport.
  - Agreed by direct message: ms-intro-2 writes both. This lane consumes `regionPairThickening` and
    `regions_of_noRegionPairDart` for `CellPocketWalk.CopyClean.regions`.
  - Asked of that statement: quantify over every pair of distinct regions, and keep "no cell-edge dart" and
    "no cell-side dart" when given.
  - This lane's green `SurgerySideSideThickeningModel` (probe 0913-181848-77014) is dropped from `.files` and not
    landed; its attic copy is 4c48e7af8.
- **Overlap with ms-binary.** `SurgeryCellHairThickening` (6ef3e9bd9, landed before T1) proves the `cell_self` half of
  T1 for cell hairs and keeps the outer invariants. T1 adds `cell_cell`, the edges between two relator faces.
  ms-binary's `CellHairThickeningSides.noCellSideDart` is exactly what T1 needs to keep the absence of cell-side darts.
- **T2 landed** (ms-cite-2, dc394dd8e): `CellSideThickening.cellSideThickening`.
- **Target Prop** (ms-cite-1): `MultipleEdgePocketRegionCopyInput` and `OsinMultipleEdgePocketRegionCopySectionStatement`.
  This lane asked for the copy to be taken of `Delta`, witness `S'.equiv`.
- **Assembly order:**
  1. T2;
  2. T1, keeping no cell-side dart;
  3. region-pair thickening, keeping both;
  4. `exists_clean_of_copy`;
  5. step 4 (ms-intro-2), step 5 (ms-intro-2, 15e21098e), step 6 (ms-intro-4);
  6. `MultipleEdgePocketRegionCopyInput`.

### Composition and invariants (18:3x–18:4x)

- **LANDED a426c4f1b** `SurgeryCellEdgeSideThickening`: probe 0913-182916-47357 GREEN, wire-queued.
  - Closed endpoint `cellEdgeSideThickening : CellEdgeSideThickeningStatement`: T1, then T2 through
    `CellSideThickening.exists_cellSideFree_of_invariant`, carrying the absence of cell-edge darts and of relator words
    of value one.
  - `copyClean_of_noDarts`: in a realized family with no cell-edge dart, no cell-side dart and no relator word of value
    one, two distinct regions joining `i ≠ j` satisfy every `CellPocketWalk.CopyClean` clause, with `regions` taken as a
    hypothesis. It uses `one_lt_cellDarts_length` (two disjoint nondegenerate arcs give the cell two darts) and
    `side_of_noCellSideDart`.
- **Why invariants.** The thickenings' opaque outputs keep only `SameTargetProfile` and `source.val`, and
  `SameTargetProfile` does not keep the target cell index. So `JoinsCells` is carried per doubling step as an
  invariant. Every transport sets `source := indexEquiv H.source` and `target := H.target.map indexEquiv`.
- **T1 invariant edit (probing).** `CellEdgeThickening.exists_cellEdgeFree_of_invariant` is added, and the plain
  `exists_cellEdgeFree` is derived from it; the statement is unchanged. Attic copy 21daf6d29.
- **Producer part 1 (probing).** `Estimating/OsinPocketCellCopyProducer.lean`, attic copy after landing:
  - `HasCellPair`;
  - `joinsCells_map`;
  - `hasCellPair_cellEdgeStep` and `hasCellPair_cellSideStep`;
  - `exists_cellEdgeSideFree_pair`.
- **Agreed with ms-intro-2.** `RegionPairThickening.exists_regionPairFree_of_invariant` will take a named one-step family
  with the same index transport, and the closed statement will gain a target-index clause. ms-intro-2 proves the
  no-cell-edge and no-cell-side `hP` instances; this lane proves the `HasCellPair` instance and the final
  `cellPocketCopyClean : CellPocketCopyCleanStatement`.

### LANDED 21b4d049d (probe 0913-183543-77148 GREEN: BUILT all 3 modules, empty error index, no `sorryAx`)

- `CellEdgeThickening.exists_cellEdgeFree_of_invariant`, additive. Rule 22 check: its only importer on origin is
  `SurgeryCellEdgeSideThickening`, which was in the same probe.
- `Estimating/OsinPocketCellCopyProducer.lean`, wire-queued: `HasCellPair`, `joinsCells_map`,
  `hasCellPair_cellEdgeStep`, `hasCellPair_cellSideStep`, `exists_cellEdgeSideFree_pair`. It gives a family with a cell
  pair, no cell-edge dart, no cell-side dart and no relator word of value one.
- **Remaining for `cellPocketCopyClean : CellPocketCopyCleanStatement`:**
  - ms-intro-2's `RegionPairThickening.exists_regionPairFree_of_invariant` (API agreed) and its `hmono` discharge;
  - then this lane's `HasCellPair` `hP` for the region-pair step;
  - then `CellEdgeSideThickening.copyClean_of_noDarts` with `RegionPairThickening.regions_of_noRegionPairDart`.
- **Named residuals of binder 5** (ms-cite-1, eb678c70a, `OsinPocketMultipleEdgeCopy`). This lane flagged them as
  unowned; main's ruling says both are owned, and this lane does not take them:
  - `CellPocketWalkOuterOffSideStatement`: w1-binder-3;
  - `CellPocketWalkSideRelatorCellStatement`: ms-inverses-2 (`cellPocketKeptCellNoncrossing`).

### Resume after the 20:03 outage (20:3x)

- Lane state checked on origin: all six modules present, disk equal to origin, last green record 0913-183543-77148.
  Nothing re-probed.
- Landed by ms-intro-2 since 18:40:
  - `SurgeryRegionPairThickeningStep` (f3a009b81): `StepData`, `stepFamily`, `stepMap`, `stepEquiv` (with
    `stepEquiv_target`), and the one-step family `RegionPairThickening.sectionFamily S f j hlen hf T`.
  - `SurgeryRegionPairThickeningCount` (9e31aea90): `one_lt_length_or_of_regions` (the `hmono` discharge),
    `stepDataOfPair`, `regionPairCount_lt`.
  - Not yet landed: `exists_regionPairFree_of_invariant`.
- This lane (probing): `CellPocketCopyProducer.hasCellPair_regionPairStep`, the `HasCellPair` instance for the
  region-pair step. It is additive in `OsinPocketCellCopyProducer`, which has no importers.
- Probe 0913-203126-12980 of `hasCellPair_regionPairStep` was lost when the MSI hop dropped (rc=255). The remote job
  stopped after its delta sync without a verdict, so it was re-probed after the control master came back.
- **Target retargeted to both orders.** ms-cite-1's `CellPocketCopyCleanBothOrdersStatement` (bdd0000bb,
  `OsinPocketMultipleEdgeCopy:264`) names this lane as owner. It is the same producer with `CopyClean b' a' i' j'`
  added: `copyClean_of_noDarts` is applied to both orders, each with its `regions` clause from
  `regions_of_noRegionPairDart` and `one_lt_length_or_of_regions`. The one-order `CellPocketCopyCleanStatement` is a
  projection. ms-torsionfree offered to build it and was told this lane holds it.
- **21:2x resume.**
  - Probe 0913-203639-55686 is GREEN (replayed on the same bytes), and `hasCellPair_regionPairStep` LANDED b349eca48.
  - ms-intro-2's `RegionPairThickening.exists_regionPairFree_of_invariant` landed at 235ce464b in
    `SurgeryRegionPairThickeningRegions`, together with `noCellEdgeDart_step` and `noCellSideDart_step`.
  - **Final producer LANDED bd7e16201.**
    - Probe 0913-213621-51846 GREEN: BUILT `OsinPocketCellCopyClean`, empty error index, no `sorryAx`.
      `cellPocketCopyClean` depends on [propext, Classical.choice, Quot.sound]. Wire-queued.
    - New module `Estimating/OsinPocketCellCopyClean.lean`, with the closed endpoints
      `cellPocketCopyCleanBothOrders : CellPocketCopyCleanBothOrdersStatement` and
      `cellPocketCopyClean : CellPocketCopyCleanStatement`.
    - Its dependencies were unchanged on origin between the probe base 6d5464e9c and the landing (checked after the
      23:12 restart).
  - Consumers whose `hcopy` binder these endpoints close (origin, 21:39):
    - both orders: `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV4` (OsinGreendlingerWaistV4), `…V4Split`,
      `multipleEdgePocketRegionCopyInput_of_pinchOrder`, `osinMultipleEdgePocketRegionCopySection_of_pinchOrder`,
      `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2CopyOrder`, the three `…OrderEuler` twins, and
      `TorsionFreeResidualsV4`;
    - one order: `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV2Copy`, `…V2CopyProper`
      (OsinPocketPinchSection), `multipleEdgePocketRegionCopyInput_of_pinch`,
      `osinMultipleEdgePocketRegionCopySection_of_pinch`, `CellPocketWalk.exists_clean_of_copy`, and
      `TorsionFreeResidualsV2Copy`.
  - The other named residuals of binder 5 belong to other lanes: `CellPocketWalkOuterOffSideStatement` (w1-binder-3),
    `CellPocketWalkSideRelatorCellStatement` (ms-inverses-2), `CellPocketPinchPosStatement` (ms-intro-4).
- Previously remaining for `cellPocketCopyCleanBothOrders` and `cellPocketCopyClean`:
  1. ms-intro-2's invariant induction;
  2. then this lane's assembly: `exists_cellEdgeSideFree_pair`, the region-pair induction with invariant
     "no cell-edge dart ∧ no cell-side dart ∧ no relator word of value one ∧ `HasCellPair`",
     `CellEdgeSideThickening.copyClean_of_noDarts` with `RegionPairThickening.regions_of_noRegionPairDart` and
     `one_lt_length_or_of_regions`.

### T3 side–side thickening (claimed, then withdrawn; see above)

CLAIM T3 side–side thickening:
- `GroupApproximation/GGT/VanKampen/SurgerySideSideThickeningModel.lean` (model test first);
- `GroupApproximation/GGT/VanKampen/SurgerySideSideThickening.lean` (statement, count, induction);
- `GroupApproximation/GGT/VanKampen/SurgeryFaceEdgeDoublingContaining.lean` (region transport).

Design:
- A **side–side dart** is a dart on a face of a region `a` of the family whose reverse lies on a face of a different
  region `b`.
- Double inside the face of `a` (a G-face). The region containing the doubled face keeps its face set through
  `faceImage`, without the digon.
- Its boundary cycle and every shelling stage map by `dartImage` (`w ↦ some none`). In a shelling step `w` lies in the
  exposed part, never in the attaching arc, because the face across `w` lies in `b`.
- `facePerm` and `alpha` commute with `dartImage` on every internal boundary move.
- `w` and `α w` lie on no contiguity arc: arcs lie on relator cells or the exterior.
- `b` transports through `DiscEmbeddingAway`.

## Residual for the binder-5 producer (cell-to-cell pocket)

- Step 3: an O-equivalent copy with legal labels satisfying cell edge conditions, then `walk.Nodup` and
  `alpha_not_mem`. This is the cell analogue of hs-vanishes' `PocketWalk.CopyClean` and
  `walk_nodup_and_alpha_not_mem`. The section version separates `Π` from the exterior face; the cell version must
  separate `Π_i` from `Π_j`. No statement is on origin.
- Step 4: orientation of the colouring, the cell analogue of cite-hull's `PocketWalkColour.walk_orient`.
- Steps 5–6: the kept cell, and the pocket region with both `FollowsBoundary` on the copy (R1). audit-sec5 owns the
  cell-to-cell face set and pinch Prop.
- Assembly target: `hull-select`'s copy form of `MultipleEdgePocketRegionInput` (drafts r1), which takes
  `CellPocketWalk.walk` as the split.
