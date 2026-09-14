# fff-quotient (lane report, 2026-09-13)

Target (ROSTER): the remaining Hyde–Lodha Proposition 4.7 pieces, other than Lemma 4.6 (hl-lemma46) and
PiFinitePresentation (kh-ejz), closed.  Consumer: `hW : FinitelyPresentedInfiniteSimpleStatement`
(simple-group's `finitelyPresentedInfiniteSimpleStatement_of_stabK`, integration point
`FinitelyPresentedInfiniteSimpleLeaves`).

## Compiled and landed
- Green probe 0913-011512-60372 (bytes = origin/main, queued for wiring):
  - `HydeLodha/QTwoFinitePresentationRestrict` (7e652b78b): `perRestrictPerm`, `exists_upsilon_split`
    (an element of `Γ₂` supported in `(c, e) + ℤ` fixing `c, d` splits over `[c, d]` and `[d, e]`).
  - `HydeLodha/QTwoFinitePresentationStabKSplit` (87b137fd3): commuting pieces and casing bounds of
    `X_Γ(c, e, S) = Υ_Γ([c, e]) ∩ Γ_S`.
  - `HydeLodha/QTwoFinitePresentationStabK` (ec1a3f2ae): `UpsilonFinitelyPresented` (Lemma 4.6 as a
    named Prop), `isFinitelyPresented_upsilon_inf_stabK`, `isFinitelyPresented_stabK_of_upsilon`.
- Green probe 0913-011741-91887 (bytes = origin/main, queued for wiring): Lemma 4.5, `|I| = 1`, for `Γ₂`.
  - `HydeLodha/QTwoFinitePresentationGermGamma` (7c39b21cf): germs of `Γ₂` at fixed grid points.
  - `HydeLodha/QTwoFinitePresentationLong` (ddd327336): `isFinitelyPresented_upsilon_gammaTwo_long`
    (`Υ_{Γ₂}([a, a + 1])` finitely presented, ascending HNN extension over the short case).
- Green probe 0913-012814-68887 (bytes = origin/main, queued for wiring):
  `HydeLodha/QTwoPropositionFourSeven` (7494328a6): `stabK_eq_stabK_addIntSet`
  (`Γ_K = Γ_{K+ℤ}` for `Γ ≤ Γ₂`), `PrintedPropositionFourSeven`, `printedPropositionFourSeven_of_upsilon`.

## Residual
Lemma 4.6, `UpsilonFinitelyPresented`, is assembled on main by the lane owners, not by this lane:
`upsilonFinitelyPresented_of_dynamics` (QTwoLemmaFourSixAssembly 3e2e73c3d, simple-group; its `|I| = 1`
case generalizes `QTwoFinitePresentationLong` to `Q₂ ≤ Γ ≤ Γ₂`) and
`lemmaFourSixDynamics : LemmaFourSixDynamicsStatement` (QTwoLemmaFourSixDynamics de535e84c, landed
unverified, probe pending).  Once that probe is green, hW is
`finitelyPresentedInfiniteSimpleStatement_of_dynamics lemmaFourSixDynamics`
(FinitelyPresentedInfiniteSimpleClosed).

## Next
The `|I| = 1` item was already landed by simple-group; this lane wrote no draft for it.

W2 hbridge, the M2 certificate cut (lead, 2026-09-13): take one separable CutFaces piece that
hull-component has not started.  hull-component answered that none is left, and main confirms it:
- the side-designated cases are `CutMove.outcome_left` (CutOutcomeSides, 27f56e14b) and
  `CutMove.outcome_right` (CutOutcomeRight, 47b7225af), which also has `CutMove.outcome`
  (probe 0913-045018-55444 GREEN);
- the source of a cut face is debt-conditional's `letterStepBound_of_cutLiftOutcome`
  (LetterPullbackCut, 457c543a8), built on `exists_geodesicCut_of_leastAreaCertificates`;
- hull-bridge's LetterPullbackHolds and EmbeddedBridgeHolds are in flight.

This lane wrote no Lean for W2.

W1 (lead, ~08:30, the only open wall): help kh-ejz on `SectionPocketFaceSetInput`
(dgo-analytic's OsinPocketPieces, 9cb70824c), and ask kh-ejz for a sub-piece before writing anything.
Asked at ~08:40.  All three candidates would go in new fff-quotient modules:
1. target positions: the `t₂` arc of `outerDarts` between the ends of `a` and `b`, with `lo_le`/`le_hi`
   against `cuts.cut j.castSucc` and `cuts.cut j.succ`, from `TargetsSectionIndex`;
2. carrier bridge: a `PocketRegion` with FollowsBoundary, the `s₁ t₁ s₂ t₂` split, the kept and source
   cells and the ε bounds, giving `Nonempty (PocketFaceSet …)`;
3. side bounds on the two region sides of an `exteriorAt` candidate.
This lane also asked whether dgo-analytic's restatement after the pinch, region, collar reorder
keeps `PocketFaceSet`.  The lead reassigned this lane before kh-ejz answered, and the offer was
withdrawn.  This lane wrote no Lean for W1.

Same-corner doubling (lead, ~10:30), for kh-torsion's `GeodesicCollarStatement` strip.  Case: a side
`s = [d]` that is a loop, `rest = []`, and `faceOf d` a monogon.  `FaceEdgeDoubling` needs a face of
length > 1, so stage 1 of the strip cannot run there.  kh-torsion was asked for the output shape stage 1
consumes (family, unboundSum, dart count, pocket faces).  The construction does not depend on that
shape: `EdgeInsertion.splitMap` at index zero turns the monogon `[d]` into a monogon `[none]` (the new
dart, labelled like `d`, standing in the place of `d`) and a value-one digon `[some none, d]`.
- `GGT/VanKampen/SurgeryMonogonDoubling` (75d0892a2, probe 0913-111910-27612 GREEN, queued for
  wiring): `MonogonDoubling.diagram`, `boundary_cellFace_darts`, `boundary_digon`,
  `boundary_digon_value`, `oEquivalent`, `reduced`, `rCellCount_eq`, `label_admissible`,
  `embedding : DiscEmbeddingAway`.
- The shape stage 1 consumes is in kh-torsion's `SurgeryGeodesicCollarAssembly` (a89b55a0d): a
  `GeodesicCollar.Transport D S Δ' S'` and a `Strip Δ' S' (s.map T.embedding) (rest.map T.embedding)`.
  It carries no family, unboundSum, dart count or pocket faces.
- `GGT/VanKampen/SurgeryMonogonDoublingStrip` (landed unverified 579226054, then fixed and landed with
  this report, probe 0913-131547-23242 GREEN, queued for wiring): `MonogonStripStatement` is
  `StripStatement` at `s = [d]`, `rest = []`, with
  `(Δ.faceBoundary (faceOf d)).darts.length = 1` and without the walk hypothesis, and
  `monogonStrip` proves it.  The strip is the digon `[d, some none]` (`collarStrip`), the face set
  is the image of `S` with the digon (`faceSet`), and `collarTransport` keeps the outer darts, the
  cell darts outside `S` and the side of every cell.

Noncrossing strip (lead, ~14:00): does kh-torsion's `GeodesicCollar.StripStatement` run on R2's `Simple`,
a noncrossing closed walk whose outer cycle follows its boundary, in place of `IsSimpleClosedWalk`?
- The sector lemma that needs inner and outer FollowsBoundary is used only to get simplicity out of a
  pocket region (`PocketRegion.ofSimpleClosedWalk_invDarts_outer`, in `geodesicCollarOutput_of_walkOutput`).
  No strip step uses it.  Stage 1 reads simplicity in two places.  The doubling transports the walk
  (`FaceEdgeDoubling.isSimpleClosedWalk_embed`).  `stripSingleton` excludes a monogon side with a
  nonempty rest (`vertexOf_alpha_ne_of_mem`, from `vertex_nodup`).
- Outer FollowsBoundary is a rotation condition (`outerTurn_iff_followsBoundary`): from each walk dart,
  the rotation reaches the reversal of the previous dart before any dart kept by the walk.  Every
  restriction of maps keeps it (`followsBoundary_outerCycle_map`), so both doublings do.  So does the vertex
  join at `x, y` with `α x` and `σ y` on the walk (`followsBoundary_outerCycle_vertexJoin`).
- `GGT/VanKampen/SurgeryNoncrossingCollarWalk` (28cdb8b0e, probe 0913-144452-8341 GREEN, queued for
  wiring): `TurnsBack`, `OuterTurn` and their transport through `VertexJoin`, restrictions and
  `EdgeInsertion`.
- `GGT/VanKampen/SurgeryNoncrossingCollarWalkSides` (dd787eba4, probe 0913-145500-75709 GREEN, queued
  for wiring): the three theorems above.
- `GGT/VanKampen/SurgeryNoncrossingCollarStrip` (landed with this report, probe 0913-153039-58042 GREEN, queued for wiring):
  `NoncrossingStrip`, `NoncrossingStripStatement`, and `noncrossingStripSingleton`, which proves the side
  `s = [d]` for any rest.  A monogon side with a nonempty rest goes through `MonogonDoubling`
  (`monogonStrip`, with the general boundary lemma `isBoundaryDart_monogonFaceSet_iff`).
- `GGT/VanKampen/SurgeryNoncrossingCollarStripModels` (landed with this report, probe 0913-153039-58042 GREEN, queued for wiring):
  - the pinched two-gon turns back (`outerTurn_pinchCycle`);
  - the lake does not (`not_outerTurn_lakeCycle`);
  - the two-petal walk `[1,3]` is noncrossing, follows outside and is not simple, and its first dart bounds
    a monogon (`monogonSideWithRestModel`);
  - the three-petal rose `[0,2,4]` passes the noncrossing fields, but its outer cycle fails
    (`roseCycle_outerCycle_not_followsBoundary`).

Residual:
- `NoncrossingStripStatement` for sides of two or more darts.  `StripStatement` has no proof either;
  only `stripSingleton` exists.
- Stages 2 and 3 read `vertex_nodup` of the strip walk (`Strip.insert_walk`, Insert:224; Join:128, 286 and
  `not_same_vertex`).  Join is the risk: under R2 the side can close a sub-walk at a repeated vertex.
- `WalkOutput` and `geodesicCollarOutput_of_walkOutput` build the pocket region with
  `ofSimpleClosedWalk`, and need a noncrossing version.

Corner join over a noncrossing walk (stage 3).  kh-torsion's `Strip.join_walk` gets simplicity of the
rest `r` in `CornerJoin` at `x = α (q.getLast)`, `y = α (p.getLast)` from `vertex_nodup`.
- `GGT/VanKampen/SurgeryNoncrossingCollarJoinModels` (e6d788879, probe 0913-162158-84746 GREEN, queued
  for wiring): `PinchedJoinModel`.  A planar one-vertex map, strip face `[0, 2]`, face set bounded by the
  noncrossing walk `[0, 4]` whose outer cycle follows its boundary, and join corners `α 2`, `α 0` in one
  rotation cycle.  So `CornerJoin`'s `not_same_vertex` can fail under R2.
- `GGT/VanKampen/SurgeryNoncrossingCollarJoin` (landed with this report, probe 0913-174832-37533 GREEN,
  queued for wiring): when the corners lie at distinct
  vertices, `r` is a noncrossing closed walk of `VertexJoin.toCombMap Δ x y` whose outer cycle follows its
  boundary (`NoncrossingStrip.join_walk`, planarity `join_planar`).  The proof carries `OuterTurn` over to
  `r` (`outerTurn_vertexJoin_rest`) and reads no `vertex_nodup`.  Its turn step
  (`exists_first_mem_vertexJoin_rest`) uses that `x` and `σ y` lie on no edge of the walk, that `p` runs
  along one face, and that `x`, `y` are not in one rotation cycle.
- Corners at one vertex: set `z = σ⁻¹ (r.head)`, pinch-split at `(x, z)`, then corner-join at `(y, z)`.
  The `p`-face leaves `S`, and `q` merges into `faceOf (r.head)`, which must be a relator face, else
  double `r.head` first.  Not in Lean.

Residual for the strip over R2:
- `NoncrossingStripStatement` for sides of two or more darts;
- the join with corners at one vertex (above);
- `Strip.insert_walk` (Insert:224) reads `vertex_nodup`;
- a noncrossing `WalkOutput` builder.

## Census
No row: these modules prove the cited group consumed at tex 1679 and do not carry a sentence (same
grading as simple-group).
