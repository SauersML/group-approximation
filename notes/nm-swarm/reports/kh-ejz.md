# kh-ejz lane report (2026-09-11/12)

Scope: property (T) of GHB(7), the `hT` leaf of kh-cckw's `ghb7LatticeRouteInput`, and the fidelity
of that statement to the manuscript's use of property (T).

## Results (relaunch 2026-09-12)

1. **Compiled bytes = origin bytes.** All ten lane files (ThreeVertexDuality, Closure, Proposition,
   Kazhdan; EJZAngleTranslates, Heisenberg, Bessel, SylowFourGram, SylowFour, GHB) match green probe
   0912-004202-1394 on origin/main; EJZAngleGHB landed f816893382e0. Nothing to land. EJZAngleSylowFour
   and EJZAngleGHB are root-wired (bfbe000c7), so `hasKazhdanPropertyT_ghb7` sits inside the root axiom
   audit.
   `GroupApproximation.KMSGroup.GHBQuotient.hasKazhdanPropertyT_ghb7 : HasKazhdanPropertyT.{0, 0} (GHB 7)`
   (Kazhdan/EJZAngleGHB.lean), under `#audit_closed_axioms`.
2. **`hT` discharged.** New module Kazhdan/GHBLatticeRouteKazhdan (in the lead's next root-wiring wave at
   green bytes 0912-093109-89237): landed 5a5886551,
   green probe 0912-092240-22748 (the normal landing reported NOTHING TO LAND, bytes identical).
   ```lean
   def PrintedGHB7PropertyT : Prop :=
     HasKazhdanPropertyT.{0, 0} (GHB 7) ∧ HasKazhdanPropertyTComplex.{0, 0} (GHB 7)
   theorem printedGHB7PropertyT : PrintedGHB7PropertyT          -- #audit_closed_axioms
   def ghb7KazhdanLatticeRouteInput (hconj : CCKWFiniteOrderConjugateIntoVertex)
       [Finite (U3 7)] [Finite (U4 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3)
       (h4 : Nat.card (U4 7) ≤ 7 ^ 4) (hhyp : Hyperbolic.IsHyperbolicGroup (GHB 7)) :
       Hyperbolic.LatticeRouteInput
   theorem sharpExistence_of_ghb7KazhdanLeaves (same binders) : Hyperbolic.SharpExistence
   ```
   Extension, landed 8085b58cd, green probe 0912-093109-89237: the same module spends `h3`, `h4`
   through `card_U3_seven_le`, `card_U4_seven_le` (Kazhdan/UnipotentSylowCounts, root-wired) and names
   the Fournier-Facio input.
   ```lean
   theorem sharpExistence_of_ghb7ConjHyp (hconj : CCKWFiniteOrderConjugateIntoVertex)
       (hhyp : Hyperbolic.IsHyperbolicGroup (GHB 7)) : Hyperbolic.SharpExistence
   theorem kotowskiOllivierStatement_of_ghb7ConjHyp (hconj : CCKWFiniteOrderConjugateIntoVertex)
       (hhyp : Hyperbolic.IsHyperbolicGroup (GHB 7)) :
       Manuscript.NonMF.TheoremC.KotowskiOllivierStatement
   ```
3. **Fidelity.**
   - Definition and universe: no gap. `HasKazhdanPropertyT.{0,0}` (real orthogonal representations on
     real Hilbert spaces in `Type`) is equivalent to the textbook complex-unitary form at every
     representation universe (`hasKazhdanPropertyT_iff_textbook`, Kazhdan/KazhdanUniverse.lean);
     `PrintedGHB7PropertyT` records both forms.
   - Manuscript: the tex names no GHB(7), no CCKW, no Kotowski–Ollivier, and prints no definition of
     (T). Property (T) enters at tex 1675 (`G_0` with property (T), citing [FFF §2]); inside [FFF §2]
     the input is an infinite finitely presented torsion-free hyperbolic group with (T).
   - Route: `TheoremC.KotowskiOllivierStatement` is `abbrev … := Hyperbolic.SharpExistence`
     (Manuscript/NonMF/FournierFacioInput.lean), the field `kotowskiOllivier` of
     `TheoremC.LiteratureInputs`, consumed as `hKO` by `HullSC.literatureInputs_of_leastAreaLeaves`
     and `manuscriptTorsionFreeTheorem_of_hullLeaves` (TorsionFreeLiteratureInputsLeastArea).
     Theorem C takes it as the hypothesis `hKO` of `TheoremC.manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs`
     and `TheoremC.manuscriptTorsionFreeSimplified_of_leastAreaInputs` (TheoremCAssembly). The former
     `sorry` `TheoremC.kotowskiOllivier` was retired at 2c3c8cb40.
   - Once `hconj` and `hhyp` are proved, `kotowskiOllivierStatement_of_ghb7ConjHyp` discharges `hKO` with GHB(7) as
     the witness. The other route is ko-closed's `kotowskiOllivier_of_leaves` (Kazhdan/KotowskiOllivierClosed).

Census: metadata/nm-census-rows/kh-ejz.tsv, LINE:1675 `partial` (does not carry the sentence).

## Remaining leaves of the GHB(7) route
- `hconj : CCKWFiniteOrderConjugateIntoVertex` (CCKW Theorem 3.1(ii), cyclic case): kh-cckw.
- `hhyp : Hyperbolic.IsHyperbolicGroup (GHB 7)` (CCKW Theorem 3.1(i)): kh-hyperbolic.
  `GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold (hzip : Systolic.ZipSpurStatement CCKW.cosetComplex)
  (hfold : Systolic.MirrorFoldStatement CCKW.cosetComplex) : Hyperbolic.IsHyperbolicGroup (GHB 7)`
  (Kazhdan/GHBHyperbolicDiscCounts, glue landed 6827a8024 unverified; waits on go-sr1's SystolicDiscFilling
  and SystolicDiscCounts) has exactly the type of the `hhyp` binder. Owners (lead ruling 2026-09-12):
  - `hzip`: `Systolic.zipSpur X : Systolic.ZipSpurStatement X` (GGT/SystolicDiscZip.lean), kh-torsion.
    It was briefly assigned to kh-ejz, which wrote no Lean and handed over its case analysis: pendant
    edge, fold of two edges at distinct vertices, and a cut vertex through
    `restrict_planar_of_euler_four`, with the `[u]` branch at outer degree 2.
  - `hfold`: `Systolic.mirrorFold X : Systolic.MirrorFoldStatement X`, fff-periodic.

## W1 pocket geometry (2026-09-13 ~04:05)
The lead's ruling on item 5 of the next section: don't build (A) or (B). hull-euler owns all of `PhiPrimeCountInput`
(C1–C6). kh-ejz does pocket geometry for W1 (a).

1. **Carrier.** By the roster reconciliation at ~04:05, dgo-analytic's `PocketRegion` (Estimating/OsinPocketRegion.lean,
   497542415) is the carrier. dgo-analytic states the piece Props in `OsinPocketPieces.lean`, which is not on main yet.
   Who discharges what:
   - kh-ejz: region-side data, for a ≠ b and for the loop;
   - kh-torsion: collar insertion;
   - hull-respell: the pinched pocket;
   - dgo-analytic: assembly and `DescentInput`.
2. **Targets** (under the collar ruling).
   - **a ≠ b.**
     - an outside face set containing the outer face, with IsDiscRegion on both sides;
     - `invDarts Δ' P.outer.cycle = s₁ ++ t₁ ++ s₂ ++ t₂`;
     - |s₁|, |s₂| ≤ ε, with no quasi-geodesic requirement on the sides;
     - t₁ and t₂ (λ,c)-quasi-geodesic;
     - a kept relator cell.
   - **Loop** (`LoopCutInput`): target = some source; the walk is s t, with s a collared side and t a cell arc. It needs
     IsDiscRegion, FollowsBoundary, a kept cell, and the `CyclicArc` datum on each cell part.
   - **go-lemma42 asks for** FollowsBoundary for the outside BoundaryCycle, and each cell part in the form
     tₖ = invDarts Δ' A.darts with A : CyclicArc (cellDarts Δ' i).
3. **Landed:** `GGT/VanKampen/Estimating/OsinPocketCellArcs` at 34342893f, after green probe 0913-044529-42148. The normal
   re-land found identical bytes. The lead wired the module into the root at 1faafe122. The five lemmas below are in
   namespace `Embedded.CyclicArc` and checked with `#audit_axioms`.
   Extension, landed e32bac3f3 after green probe 0913-052330-1543, also checked with `#audit_axioms`:
   ```lean
   def CyclicArc.rest (arc : CyclicArc cycle) : CyclicArc cycle  -- starts where arc ends
   theorem CyclicArc.rest_length (arc : CyclicArc cycle) : arc.rest.length = cycle.length - arc.length
   theorem CyclicArc.rotated_eq_darts_append_rest_darts (arc : CyclicArc cycle) :
       arc.rotated = arc.darts ++ arc.rest.darts
   theorem ContiguityGeometry.invDarts_rightSide_length_le (H : ContiguityGeometry D eps Delta faces) :
       (invDarts Delta H.rightSide).length ≤ eps
   theorem ContiguityGeometry.invDarts_leftSide_length_le (H : ContiguityGeometry D eps Delta faces) :
       (invDarts Delta H.leftSide).length ≤ eps
   ```
   The side bounds give |s₁|, |s₂| ≤ ε for a side read across `alpha`.
   New module `GGT/VanKampen/Estimating/OsinPocketFollowsBoundary`, landed unverified at d2b2ef55b. Its green probe
   0913-055258-46066 matched the same bytes. It is not wired, because it imports the unwired OsinPocketRegionRotate.
   It answers go-lemma42's request (i), under `#audit_axioms`:
   ```lean
   theorem BoundaryCycle.followsBoundary_congr (h : boundary.boundaryPerm = boundary'.boundaryPerm) :
       boundary.FollowsBoundary ↔ boundary'.FollowsBoundary
   theorem BoundaryCycle.followsBoundary_ofIsRotated_iff (h : boundary.cycle ~r l) :
       (boundary.ofIsRotated h).FollowsBoundary ↔ boundary.FollowsBoundary
   theorem IsDiscRegion.followsBoundary_ofIsRotated_iff (h : region.cycle ~r l) :
       (region.ofIsRotated h).FollowsBoundary ↔ region.FollowsBoundary
   theorem FaceSetCircuits.toDiscRegion_followsBoundary (c : Component M faces) (hall) (hM : M.IsPlanar) :
       (toDiscRegion M faces c hall hM).FollowsBoundary
   theorem PocketRegion.withOuter_outer_followsBoundary_iff (h : invDarts Delta P.outer.cycle ~r l) :
       (P.withOuter h).outer.FollowsBoundary ↔ P.outer.FollowsBoundary
   ```
   So the complement follows the boundary whenever it is built by `toDiscRegion` and then restarted with
   `withOuter`. I told go-lemma42 at ~05:55.
   The five cell-arc lemmas:
   ```lean
   theorem invDarts_darts (arc : CyclicArc cycle) : invDarts Delta arc.darts = arc.reverseDarts
   theorem dartWord_darts_cellDarts (arc : CyclicArc (cellDarts Delta i)) :
       dartWord Delta arc.darts = ((cell Delta i).word.rotate arc.start.1).take arc.length
   theorem dartWord_invDarts_darts_cellDarts (arc : CyclicArc (cellDarts Delta i)) :
       dartWord Delta (invDarts Delta arc.darts) =
         RelWord.revInv (((cell Delta i).word.rotate arc.start.1).take arc.length)
   theorem isLambdaCQuasiGeodesicWord_darts_cellDarts (hcond : OsinCCondition D W eps mu lambda c rho)
       (arc : CyclicArc (cellDarts Delta i)) : IsLambdaCQuasiGeodesicWord D lambda c (dartWord Delta arc.darts)
   theorem isLambdaCQuasiGeodesicWord_invDarts_darts_cellDarts (hcond : OsinCCondition D W eps mu lambda c rho)
       (arc : CyclicArc (cellDarts Delta i)) :
       IsLambdaCQuasiGeodesicWord D lambda c (dartWord Delta (invDarts Delta arc.darts))
   ```
   - Once a cell part is `invDarts Δ' A.darts`, hquasi for t₁ and t₂ follows from these.
   - `OsinCCondition` is available to the producer: `OsinMultipleEdgeCutSectionStatement` and
     `OsinLoopCutSectionStatement` (OsinAppendixGreendlingerParts.lean:46-70) quantify
     `∀ W, OsinCCondition … → MultipleEdgeCutInput …`, and likewise for `LoopCutInput`. So there is no gap.
4. **Residual (mine): the region-side geometry.**
   - Starting point: two distinct regions a ≠ b in S.family join cells i ≠ j. They are face-disjoint, and their arcs
     on a cell are disjoint by `RegionCandidate.cellArcDarts_disjoint`.
   - Rulings (~06:30). The lead: state the Prop myself over `PocketRegion`, uncollared, on Δ; do a ≠ b first;
     LoopCutInput is on HOLD. dgo-analytic: the split is uncollared, the sides are the ContiguityGeometry sides with
     length and word norm ≤ ε, and the kept cell (the m₁ = 0 exclusion by merging a and b) is part of my discharge.
   - **Stated:** new module `GGT/VanKampen/Estimating/OsinPocketRegionSide`, landed unverified at d00f94876. Green
     probe 0913-064335-8857 on the same bytes. It is unwired, since it imports the unwired OsinPocketRegion.
     ```lean
     def MultipleEdgePocketRegionInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
         (W : Set (List (RelLetter G Lambda))) : Prop :=
       -- binders of MultipleEdgeCutInput, then
       ∃ (P : PocketRegion S.diagram) (C : RelatorCell S.diagram.toCombMap S.diagram.outerFace W)
         (s₁ s₂ : List S.diagram.toCombMap.Dart)
         (A₁ : CyclicArc (cellDarts S.diagram i)) (A₂ : CyclicArc (cellDarts S.diagram j)),
         C ∈ S.diagram.relatorCells ∧ C.face ∈ P.faces ∧
           (cell S.diagram i).face ∉ P.faces ∧ (cell S.diagram j).face ∉ P.faces ∧
           invDarts S.diagram P.outer.cycle =
             s₁ ++ invDarts S.diagram A₁.darts ++ s₂ ++ invDarts S.diagram A₂.darts ∧
           s₁.length ≤ eps ∧ s₂.length ≤ eps ∧
           wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord S.diagram s₁)) ≤ eps ∧
           wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord S.diagram s₂)) ≤ eps ∧
           P.inner.FollowsBoundary ∧ P.outer.FollowsBoundary
     ```
   - Consumer: `OsinMultipleEdgeCut.ofPocketRegion` with `equiv := S.equiv` and `C' := cell S.diagram i`. hquasi on
     the arc parts comes from OsinPocketCellArcs, and on the sides only after kh-torsion's collar.
   - ~06:45: I sent the name to dgo-analytic to adopt in OsinPocketPieces, and to dgo-geometric for the model test.
     The three risks I raised:
     - pinched pockets, with sides touching at a vertex;
     - a non-simple cell boundary in the gap, where the arc part may be two intervals rather than one CyclicArc;
     - merge absorption of third regions inside the pocket.
   - **Gap arcs** (the list-level part of the pocket walk): new module `GGT/VanKampen/Estimating/OsinPocketGapArcs`,
     landed unverified at b389a81cf. Green probe 0913-073424-67369 ran on the same bytes (md5 checked). It is unwired.
     All four declarations below are under `#audit_axioms`:
     ```lean
     def CyclicArc.shorten (arc : CyclicArc cycle) (m : ℕ) (hm : m ≤ arc.length) : CyclicArc cycle
     theorem CyclicArc.shorten_darts : (arc.shorten m hm).darts = arc.darts.take m
     theorem CyclicArc.rest_darts (arc : CyclicArc cycle) : arc.rest.darts = arc.rotated.drop arc.length
     theorem CyclicArc.exists_gapArcs (X Y : CyclicArc cycle) (hX : 0 < X.length)
         (hXY : ∀ d ∈ X.darts, d ∉ Y.darts) :
         ∃ G₁ G₂ : CyclicArc cycle, G₁.start = X.rest.start ∧ G₂.start = Y.rest.start ∧
           X.rotated = X.darts ++ G₁.darts ++ Y.darts ++ G₂.darts
     ```
     - It needs no duplicate-free hypothesis, because overlapping positions share a dart.
     - It applies to `cellDarts Δ i`, giving the cell part t₁.
     - It also applies to `outerDarts Δ`, giving t₂ of the section pocket.
5. **Item `SectionPocketFaceSetInput`** (lead, ~08:30; fff-quotient joins as helper).
   - The Prop (OsinPocketPieces.lean:161, dgo-analytic): two distinct exterior regions `a ≠ b` of cell `i` to section
     `j`, in a `GloballyDistinguishedSectionFamily`, give `Nonempty (PocketFaceSet D eps S.diagram lo hi)`.
   - Planar separation on main: `simpleClosedWalkSides` (GGT/VanKampen/SimpleClosedWalkSides, 79008d7e5 and
     4dce22f1e). Both sides of a simple closed walk in a planar map are disc regions. A pinched walk is not covered.
   - **Landed:** new module `GGT/VanKampen/Estimating/OsinPocketSectionFaceSet`.
     - v1 landed unverified at 22c13e69c; green probe 0913-091517-29709 on the same bytes.
     - v2 (the pocket walk) lands with this report, after green probe 0913-094356-29530 on the same bytes. It is
       unwired.
     - v2 renames the v1 helper `PocketFaceSet.outerFace_not_mem_sideFaces` to
       `outerFace_not_mem_sideFaces_of_mem_outerDarts`, because dgo-analytic's OsinPocketRegionOfSimple declares the
       old name.
     - All declarations below are under `#audit_axioms`:
     ```lean
     theorem CyclicArc.exists_spanArc (X Y : CyclicArc cycle) (hX : 0 < X.length)
         (hXY : ∀ d ∈ X.darts, d ∉ Y.darts) :
         ∃ Gap T : CyclicArc cycle, Gap.start = X.rest.start ∧ T.start = X.start ∧
           T.darts = X.darts ++ Gap.darts ++ Y.darts
     theorem CyclicArc.exists_transport (f : α → List Dart) (h : a₁ = a₂) (arc : CyclicArc (f a₁)) :
         ∃ arc' : CyclicArc (f a₂), arc'.start.1 = arc.start.1 ∧ arc'.length = arc.length ∧
           arc'.darts = arc.darts
     noncomputable def PocketFaceSet.ofSimpleClosedWalk (source kept) (sourceArc) (targetArc)
         (firstSide secondSide)
         (hw : IsSimpleClosedWalk X.toCombMap
           (firstSide ++ invDarts X sourceArc.darts ++ secondSide ++ targetArc.darts))
         (hsource : 0 < sourceArc.length) (htarget : 0 < targetArc.length)
         (hkept : (cell X kept).face ∈ sideFaces X.toCombMap (…)) (side bounds) (hlo) (hhi) :
         PocketFaceSet D eps X lo hi                                  -- faces := sideFaces, boundary := hw.innerCycle
     theorem PocketFaceSet.ofSimpleClosedWalk_simple : (ofSimpleClosedWalk …).Simple
     structure PocketWalk (D) (eps) (X) (lo hi : ℕ)   -- source, sourceArc, targetArc, firstSide, secondSide, bounds
     def PocketWalk.walk (K) := K.firstSide ++ invDarts X K.sourceArc.darts ++ K.secondSide ++ K.targetArc.darts
     noncomputable def PocketWalk.toPocketFaceSet (K) (kept) (hw : IsSimpleClosedWalk X.toCombMap K.walk)
         (hkept : (cell X kept).face ∈ sideFaces X.toCombMap K.walk) : PocketFaceSet D eps X lo hi
     theorem PocketWalk.exists_of_exteriorAt (S : RealizedSectionFamily D lambda c eps Delta cuts)
         (ha : a ∈ exteriorAt S.family i) (hb : b ∈ exteriorAt S.family i) (hab : a ≠ b)
         (hja : TargetsSectionIndex cuts j a) (hjb : TargetsSectionIndex cuts j b) :
         ∃ (K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ)) (x y),
           (x = a ∧ y = b ∨ x = b ∧ y = a) ∧ K.source = i ∧ K.firstSide = y.2.leftSide ∧
           K.secondSide = x.2.rightSide ∧
           (∃ Gap, K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts) ∧
           K.targetArc.start.1 = x.2.targetArc.start.1 ∧
           K.targetArc.start.1 + K.targetArc.length = y.2.targetArc.start.1 + y.2.targetArc.length
     ```
   - Orientation: `x` is the region whose outer arc starts first. `t₁` runs forward on `∂Π_i` from `x`'s source arc to
     `y`'s, and `t₂` runs on `∂X` from the start of `x`'s outer arc to the end of `y`'s.
   - **Residual** for `SectionPocketFaceSetInput`, given `exists_of_exteriorAt`:
     - (i) `IsNoncrossingClosedWalk S.diagram.toCombMap K.walk`. Simplicity (`IsSimpleClosedWalk`) is false in general:
       a pinched pocket repeats a vertex. hull-respell's `PocketPinchStatement` and its reduction
       `PocketPinchPinchedStatement` (OsinPocketPinchUnpinched) both take a `PocketFaceSet` as input, so the pinched
       case still needs a face set first.
       **P2' landed with this report** (green probe 0913-111928-29730): new module `GGT/VanKampen/NoncrossingClosedWalkSides`,
       unwired. `IsNoncrossingClosedWalk` asks for distinct darts, no edge used in both directions, and a turning
       condition: rotating from `alpha d` for a walk dart `d`, the first dart on a walk edge is a walk dart. The
       restriction to the walk edges is then connected (`PermFirstReturn.sameCycle_iff`), its faces advance along walk
       darts, and the separation proof of SimpleClosedWalkSides goes through unchanged.
       ```lean
       def NoncrossingClosedWalkSidesStatement : Prop :=
         ∀ (M : CombMap) (w : List M.Dart), M.IsPlanar → IsNoncrossingClosedWalk M w →
           ∃ (faces outside : Finset M.Face) (inner : BoundaryCycle M faces) (outer : BoundaryCycle M outside),
             (∀ f, f ∈ outside ↔ f ∉ faces) ∧ inner.cycle = w ∧ outer.cycle = w.reverse.map M.alpha
       theorem noncrossingClosedWalkSides : NoncrossingClosedWalkSidesStatement   -- #audit_closed_axioms
       theorem IsSimpleClosedWalk.isNoncrossingClosedWalk (hw : IsSimpleClosedWalk M w) : IsNoncrossingClosedWalk M w
       ```
       No `FollowsBoundary` claim: a pinched cycle need not follow its face set
       (`OsinPocketPinchedTwoGonModel.not_followsBoundary`).
       Consumers added to OsinPocketSectionFaceSet (additive, `#audit_axioms`): `PocketFaceSet.ofBoundaryCycle` (any
       face set whose boundary cycle is `s_1 t_1 s_2 t_2` and which contains a relator cell),
       `PocketFaceSet.ofNoncrossingClosedWalk`, `PocketWalk.toPocketFaceSetOfNoncrossing`, and
       `toPocketFaceSetOfNoncrossing_cycle` (the boundary cycle is `K.walk`).
       Open: the turning condition for `K.walk`. P2' does not touch (iii): a walk holding both darts of an edge
       violates `alpha_not_mem`.
       **Model test landed with this report** (green probe 0913-125753-37346): new module
       `Estimating/OsinPocketPinchedTwoGonNoncrossing`, unwired. The cycle `[5,3,4,6]` of the pinched pocket of
       OsinPocketPinchedTwoGonRegion is noncrossing and not simple (`pocket_noncrossing_not_simple`): one rotation step
       from the reversal of each walk dart reaches a walk dart (`1 ↦ 6`, `0 ↦ 4`, `8 ↦ 3`, `9 ↦ 5`). Its side face set
       is the pocket face set (`sideFaces_pocket`). So the carrier covers the pinch that `IsSimpleClosedWalk` excludes.
       Additive in NoncrossingClosedWalkSides: `turn_mem_of_first`, the turning condition at one dart from the first
       walk edge met when rotating from its reversal.
     - (ii) the kept cell on the side of the walk. Without it, the pocket holds no relator cell, and hull-select's
       zero-cell merge should contradict weight maximality. `OsinPocketZeroCellMerge` (`innerBoundary`,
       `toInnerGRegion`, `mergedGeometry`) is on main. The contradiction module `OsinPocketZeroCellMergeFalse`, which
       its docstring names, is not.
     - (iii) **Construction gap, reported to main with a ruling request.** `cycle_mem_iff` forbids a dart and its
       reverse in one boundary cycle. The pocket walk contains both darts of an edge in three configurations that
       `DiscDiagram` allows:
       - (a) a spur of section `j` between the two targets. Both darts are `outerDarts` with `faceOf = outerFace`.
         `OEquivalentDiscDiagram` keeps `boundaryWord`, and `SurgeryFaceEdgeDoubling` needs `f ≠ outerFace`.
       - (b) an edge of the gap arc with cell `i` on both sides.
       - (c) `x.right` sharing an edge with `y.left` behind the cell.
       The manuscript's `Γ_1`, with sides `inv y.right` and `inv x.left`, avoids (c) only. No model test was run.
       Options put to main:
       - (A) keep the statement, build P2', and rule (a)–(c) out;
       - (B) produce the face set on an O-equivalent copy, with a boundary edge doubling for spurs;
       - (C) merge the Prop with `PocketPinchStatement`.
   - When hull-euler's C6 Prop arrives, check it against this output.

## W1 assignment (2026-09-13 ~03:00)
The lead's order: work on W1 hgreendlinger. hull-euler owns `PhiPrimeCountInput` alone, so take one separable part
that hull-euler has not started. Land the statement first, then the proof.

1. **Piece taken.** The pure CombMap half of the Euler count in Osin's Lemma 9.3, allowing multiple edges.
   - Φ'_M can join one cell to one section by several edges, so `SubdividedGraph.noMultiple` fails for it.
   - Proposed to hull-euler in msg 5f03541a. There was no reply before landing.
2. **Landed.**
   - The statement landed unverified at 69c4c69da.
   - The proof landed at 04240bd43 after green probe 0913-032002-45119, with no warnings.
   - The module is `GGT/VanKampen/Estimating/OsinAppendixEulerMultigraph`. It is queued for wiring; its only import,
     OsinAppendixEulerSubdivided, is already on main.
   ```lean
   structure SubdividedMultigraph (ρ : Type w) (C : Type z)   -- SubdividedGraph without noMultiple
   def SubdividedGraph.toSubdividedMultigraph (S : SubdividedGraph M ρ C) : SubdividedMultigraph M ρ C
   def SubdividedMultigraph.IsTwoGon (f : M.Face) : Prop :=
     ∃ d : M.Dart, S.IsCellDart d ∧ M.faceOf d = f ∧
       M.facePerm (M.facePerm (M.facePerm (M.facePerm d))) = d ∧
         S.region (M.facePerm (M.facePerm d)) ≠ S.region d
   theorem subdividedMultigraphFace : SubdividedMultigraphFaceStatement             -- #audit_closed_axioms
   theorem midpointCountTwoGon : MidpointCountTwoGonStatement                       -- #audit_closed_axioms
   theorem edgeBoundSubdividedMultigraph : EdgeBoundSubdividedMultigraphStatement   -- #audit_closed_axioms
   theorem edgeBound_of_subdividedMultigraph (S : SubdividedMultigraph M ρ C) (hplanar : M.IsPlanar)
       {c m : ℕ} (hdarts : M.dartCount = 4 * m) (hvertices : M.vertexCount ≤ c + m) :
       m + 6 ≤ 3 * c + (Finset.univ.filter fun f : M.Face => M.faceDegree f < 6).card
   ```
3. **Route.**
   - Every face has degree at least four. Odd iterates change the kind of a dart, and a two-step face would join a
     cell to itself.
   - Take a face of degree less than six through a cell dart `d`. By `six_le_faceDegree`, `facePerm⁴ d = d`.
   - If the two regions of that face coincide, the region runs out and back, and both end cells hold only that
     region. The map then has at most four darts (`dartCount_le_four_of_facePerm_four`).
   - Euler's formula with `6F ≤ 4m + 2t` and `V ≤ c + m` gives `m + 6 ≤ 3c + t`.
4. **Residual in `PhiPrimeCountInput`** (hull-euler's).
   - Build Φ'_M as a `SubdividedMultigraph`.
   - Bound `t`, the number of two-gons, through (∗).
   - Nesting caveat, sent to hull-euler: the restricted map drops untouched cells, so a degree-4 face can enclose
     cells and components.
   - Proposed charge (not proved):
     - two-gons that straddle a cut number at most r;
     - every other pocket has a nonempty, region-closed, disjoint cell set C_P holding at most 3(|C_P| − 1) regions;
     - with one outer-face vertex, the total is at most 3n + r − 3.
5. **Next.** hull-euler has not replied, and its report on main ends "Whether hull-euler takes on
   `PhiPrimeCountInput` is the lead's call." So on 2026-09-13 at ~03:50 I sent the lead a proposed split:
   - (A) The Φ'_M builder: `phiSubdividedGraph` with the exterior regions kept, and the outer face of `collapsedMap`
     as one vertex. `RegionCandidate.cross` already gives crossing darts on an exterior target arc.
   - (B) The bound on `t`:
     - there are at most r straddling two-gons;
     - a same-section pocket with no R-cell is contradicted by `false_of_collapse_singleton` (OsinAppendixCutMerge);
     - a pocket holding an R-cell is charged to a cell that is not an endpoint.
   - `NoMultipleEdges` covers only pairs of cells (`JoinsCells`), so (B) does not follow from the hypotheses.
   - With `t ≤ r + (n − endpoint cells)`, the count gives `|M| ≤ 3n + r − 3 ≤ 3(n + r − 1)`.
   The lead's ruling: don't build (A) or (B), because hull-euler owns all of `PhiPrimeCountInput`. See "W1 pocket geometry"
   above.
6. **Text fix, landed 46f1c36a2** (green probe 0913-034435-10433), from sec2-sentences's stale-mention backlog. Three
   texts now say Theorem C takes `KotowskiOllivierStatement` as the hypothesis `hKO`:
   - the GHBLatticeRouteKazhdan docstring;
   - the census row for tex line 1675;
   - the Fidelity item under Results.
   No Prop changed.

## Current assignment (2026-09-13)
Roster: target PiFinitePresentation (the finite-presentation transfer `hW` needs), then row LINE:1675 with
nm-endpoints.

1. **PiFinitePresentation is closed and landed.** It is the product step of Proposition 4.7 below:
   `isFinitelyPresented_sup_of_commute` and `isFinitelyPresented_of_commutator_le`
   (QTwoFinitePresentationProduct), landed ba54a571f, green probe 0912-103148-88562. fff-quotient's
   `isFinitelyPresented_stabK_of_upsilon` (QTwoFinitePresentationStabK, ec1a3f2ae) consumes it. No new
   landing is needed for the target.
2. **`hW` residual on origin/main.** `HydeLodha.FinitelyPresentedInfiniteSimpleLeaves := StabKFinitelyPresented qTwo`
   (GroupTheory/HydeLodha/FinitelyPresentedInfiniteSimpleLeaves.lean, 65dd38c11).
   `isFinitelyPresented_stabK_of_upsilon hU le_rfl qTwo_le_gammaTwo` reduces that leaf to Hyde–Lodha
   Lemma 4.6, which is open:
   ```lean
   def UpsilonFinitelyPresented : Prop :=
     ∀ Γ : Subgroup (Equiv.Perm ℚ), qTwo ≤ Γ → Γ ≤ gammaTwo → ∀ a b : ℚ, (∃ M, a ∈ Grid 6 M) →
       (∃ M, b ∈ Grid 6 M) → a < b → b ≤ a + 1 → Group.IsFinitelyPresented ↥(upsilon Γ a b)
   ```
   hl-lemma46b's in-flight copy (attic/inflight/hl-lemma46b/.../FinitelyPresentedInfiniteSimpleLeaves.lean.txt)
   re-points the leaf at `UpsilonFinitelyPresented`.
3. **Lemma 4.6 on origin/main.**
   - At `Γ = Γ₂` (Lemma 4.5): `isFinitelyPresented_upsilon_gammaTwo_short`, `_unit`
     (QTwoFinitePresentationShort), `isFinitelyPresented_upsilon_gammaTwo_long` (QTwoFinitePresentationLong).
   - Case 1 helpers (QTwoLemmaFourSixCaseOne, 44d75dddd): `upsilonc`, `upsilon_commutator_inter_upsilonc`,
     `pow_conj_mem_commutator_upsilon`.
   - Twisted generators, `H ≅ F₆` (QTwoLemmaFourSixGenerators, 7db72cfc1): `exists_twisted_generators`.
   - Tools: `isFinitelyPresented_of_casingPair` (GroupTheory/CasingPair), `isFinitelyPresented_of_ascending`
     (GroupTheory/AscendingHNNRecognition).
   - Piece statements (QTwoLemmaFourSixStatements, simple-group, 232d6b12b): `LemmaFourSixDynamicsStatement`,
     `LemmaFourSixCaseOneStatement`.
   Owners (lead, 2026-09-13):
   - hl-lemma46: dynamics.
   - simple-group: Case 1 and the final assembly.
   - fff-quotient: `|I| = 1`, as an ascending HNN extension.
   - kh-ejz: the casing pair `Υ_{Γ₂}(I)' ≤ N ≤ Υ_Γ(I) ≤ Υ_{Γ₂}(I)` through `isFinitelyPresented_of_commutator_le`,
     plus conjugation of a general `[a, b]` with `|I| < 1` into the unit frame, consuming
     `LemmaFourSixCaseOneStatement`.
4. **Row LINE:1675** is carried by `fournierFacioParagraph_of_leastAreaLeaves (hgreendlinger) (hbridge) (hKO) (hW)`
   (TorsionFreeLiteratureInputsLeastArea). It flips only when all four walls close. nm-endpoints owns the flip.
5. **Wiring.** QTwoFinitePresentationProduct and QTwoFinitePresentationNormal (mine, ba54a571f) are queued in
   the lead's wire queue. fff-quotient's Restrict, StabKSplit and StabK were already queued.
6. **Superseded route.** Before the re-split the lead assigned me Case 2 (`|I| = 1`) through `Υ'' = Υ'`.
   - Its statement `LemmaFourSixCaseTwo` (QTwoLemmaFourSixCaseTwo, statement only) landed as an orphan at
     9711ad726.
   - The docstring now says the route is superseded and nothing consumes it (landed 5fd45c0bf after green probe
     0913-020001-45307; attic copy 313612b9f).
   - The perfectness lemma for `|I| = 1` was never written.
7. **My piece, landed unverified at 58cfe133e** (QTwoLemmaFourSixTransfer):
   ```lean
   def UpsilonShortOfCaseOne : Prop :=
     LemmaFourSixCaseOneStatement →
       ∀ Γ : Subgroup (Equiv.Perm ℚ), qTwo ≤ Γ → Γ ≤ gammaTwo → ∀ a b : ℚ, (∃ M, a ∈ Grid 6 M) →
         (∃ M, b ∈ Grid 6 M) → a < b → b < a + 1 → Group.IsFinitelyPresented ↥(upsilon Γ a b)
   theorem upsilonShortOfCaseOne : UpsilonShortOfCaseOne
   ```
   - Lemmas: `isFinitelyPresented_upsilon_unit_of_caseOne` (the casing pair in the unit frame) and
     `isFinitelyPresented_upsilon_short_of_caseOne` (conjugation into the unit frame).
   - The audit is `#audit_axioms`: the Prop is conditional on Case 1, so it is not a closed endpoint.
   - Green probe 0913-020001-45307 (QTwoLemmaFourSixTransfer and QTwoLemmaFourSixCaseTwo, no warnings). Axioms
     of `upsilonShortOfCaseOne`: `[propext, Classical.choice, Quot.sound]`.
   - Consumed unchanged by simple-group's QTwoLemmaFourSixAssembly (3e2e73c3d, green probe 0913-021204-99418),
     through `isFinitelyPresented_upsilon_short_of_caseOne` in `upsilonFinitelyPresented_of_caseOne`.
     simple-group needs no further Lean from me on Lemma 4.6.
   - Per simple-group, `LemmaFourSixDynamicsStatement` (hl-lemma46) is the only open leaf under hW.

## Assignment (2026-09-12)
Hyde–Lodha Proposition 4.7, alongside fff-quotient:
`HydeLodha.StabKFinitelyPresented Γ` (GroupTheory/HydeLodha/QTwoFinitelyPresented.lean). Edits to the rooted
Q2 modules (QTwoFinitelyPresented, QTwoFinitePresentationShort, QTwoBrownTriangle,
QTwoFinitePresentationLong) land NM_ATTIC until green.

Split agreed with fff-quotient. kh-ejz writes two orphan modules. fff-quotient's QTwoFinitePresentationStabK
(induction over `Finset.induction_on_max`) imports both and uses these exact names and binders. kh-ejz
stays out of Restrict, StabK, StabKSplit, Derived and the L4.6 assembly. Landed ba54a571f,
green probe 0912-103148-88562 (base a5013a01c, both modules BUILT, `stabK_eq_upsilon_inf_stabK` on
propext, Classical.choice, Quot.sound). fff-quotient's QTwoFinitePresentationStabK (ec1a3f2ae) consumes all
seven statements below.

`GroupTheory/HydeLodha/QTwoFinitePresentationProduct.lean` ("R = ∏ …; R' ⊆ R₁ ⊆ Γ_K ⊆ R; casing pair"):
```lean
def commuteSupHom {G : Type*} [Group G] (A B : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) : ↥A × ↥B →* G
theorem range_commuteSupHom … : (commuteSupHom A B hcomm).range = A ⊔ B
theorem isFinitelyPresented_sup_of_commute {G : Type*} [Group G] (A B : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) (hdisj : A ⊓ B = ⊥)
    [Group.IsFinitelyPresented ↥A] [Group.IsFinitelyPresented ↥B] :
    Group.IsFinitelyPresented ↥(A ⊔ B)
theorem isFinitelyPresented_of_commutator_le {G : Type*} [Group G] (N H K : Subgroup G)
    (hNH : N ≤ H) (hHK : H ≤ K) (hKN : ⁅K, K⁆ ≤ N) [Group.FG ↥K]
    [Group.IsFinitelyPresented ↥N] : Group.IsFinitelyPresented ↥H
theorem commutator_sup_le_of_commute {G : Type*} [Group G] (A B N : Subgroup G)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) (hA : ⁅A, A⁆ ≤ N) (hB : ⁅B, B⁆ ≤ N) :
    ⁅A ⊔ B, A ⊔ B⁆ ≤ N
```
`GroupTheory/HydeLodha/QTwoFinitePresentationNormal.lean` ("Since Γ is 1-periodic, Γ_K = Γ_{K+ℤ}"):
```lean
def normalShift (k₀ t : ℚ) : ℚ := k₀ + Int.fract (t - k₀)
theorem normalShift_mem_Ioo {k₀ t : ℚ} (ht : normalShift k₀ t ≠ k₀) :
    k₀ < normalShift k₀ t ∧ normalShift k₀ t < k₀ + 1
theorem dyadic6_normalShift {k₀ t : ℚ} (ht : Dyadic6 t) : Dyadic6 (normalShift k₀ t)
theorem stabK_eq_upsilon_inf_stabK {Γ : Subgroup (Equiv.Perm ℚ)} (hΓ : Γ ≤ gammaTwo)
    {K : Set ℚ} {k₀ : ℚ} (hk₀ : k₀ ∈ K) :
    stabK Γ K = upsilon Γ k₀ (k₀ + 1) ⊓ stabK Γ (normalShift k₀ '' K \ {k₀})
```
Model check at K = {k₀}: K' = ∅, so `stabK Γ {k₀} = upsilon Γ k₀ (k₀ + 1)`. The commutator bound needs no
normality of N, because ⁅a₁b₁, a₂b₂⁆ = ⁅a₁, a₂⁆⁅b₁, b₂⁆ when A and B commute.

## Landing rule
Edits to EJZAngleGHB, EJZAngleSylowFour and GHBLatticeRouteKazhdan land with NM_ATTIC until a probe is
green, never NM_UNVERIFIED.

## Model test (scratch Python, not landed)
- Regular-representation angles of the CCKW Prop 7.15 images in SL4(F7): <a,b> (343) 0.377964 = 1/√7;
  <c,b>, <c,a> (2401) 0.534522 = √(2/7).
- 1/√2 (HeisenbergAngleBound) FAILS both EJZ Cor 3.3 and Thm 5.9 for GHB(7).
- Sharp angles pass Cor 3.3: eps0 = 0.958 < 1.  Rational constants: e3 = 0.378, e1 = e2 = 0.5346,
  eps0 = 0.96.
- U4 key inequality Σ_{0<m<p} ⟨x, b^m x⟩ / ‖x‖² ≤ 0.22 on samples (claim ≤ 1).

## GREEN, landed
- PropertyT/ThreeVertexDuality: EJZ Lemma 2.4 (density form), Lemma 2.5.
- PropertyT/ThreeVertexClosure: closures, EJZ (3.3), two-subspace estimate.
- PropertyT/ThreeVertexProposition: EJZ Prop 3.2 in Hilbert form (density replaces X + Y = U).
- PropertyT/ThreeVertexKazhdan: MovingAngleLE, isKazhdanSubset_of_movingAngles (EJZ Cor 3.3(a)).
- Kazhdan/EJZAngleTranslates: translate sums; twisted fixed vectors orthogonal off V^z.
- Kazhdan/EJZAngleHeisenberg: movingAngleLE_heisenberg (1/√p, CCKW Prop 7.3(i), character-free).
- Kazhdan/EJZAngleBessel: Bessel for translate sums over transversal cyclic subgroups; w^i z^j calculus.
- Kazhdan/EJZAngleSylowFourGram: a b^m = b^m a w^m z^{m(m-1)/2}; Gram-sum bound for U4(p).
- Kazhdan/EJZAngleSylowFour: movingAngleLE_sylowFour (√(2/p), CCKW Prop 7.3(ii), character-free).
- Kazhdan/EJZAngleGHB: hasKazhdanPropertyT_ghb7.
- Kazhdan/GHBLatticeRouteKazhdan: PrintedGHB7PropertyT, sharpExistence_of_ghb7KazhdanLeaves,
  sharpExistence_of_ghb7ConjHyp, kotowskiOllivierStatement_of_ghb7ConjHyp.

## TRAPS
- `omit [..] in` must precede the docstring, not sit between docstring and theorem.
- `Finset.add_sum_erase _ _ h` cannot infer the summand: pass the lambda explicitly.
- `gcongr` may discharge side goals itself; following `·` bullets then fail with "no goals".
- Unused simp args are errors (`simp [real_inner_self_eq_norm_sq]` when simp closes without it).
