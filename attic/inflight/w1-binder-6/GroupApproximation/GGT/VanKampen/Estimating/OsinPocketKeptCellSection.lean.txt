import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFaceSetOnCopy
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellKeptCellNoncrossing
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeModel
import GroupApproximation.Meta.AxiomGuard

/-!
# The kept relator cell of the pocket walk of two exterior regions

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two exterior regions of a cell `Π` to one section holds an
`R`-cell, since otherwise the two regions merge, against the choice of the distinguished system.

`GloballyDistinguishedSectionFamily.exists_kept_of_pocketRegion_of_value`
(`Estimating/OsinPocketKeptCellAbsorbed`) gives a relator cell in any pocket region whose cycle is
the walk.  A pocket region is two disc regions, and a disc region is a boundary cycle whose
reclosing keeps the Euler characteristic (`BoundaryCycle.toDiscRegion_of_euler`).  So the pocket
region of a noncrossing walk needs only the Euler equalities of its two reclosings
(`PocketRegion.ofNoncrossingClosedWalkEuler`).

Why the residual is stated through Euler equalities and not through following cycles.  At a joint
inside a side, or at a corner, the inner sector holds only internal darts of the region, so the
inner cycle follows there; a touch at such a vertex breaks the outer cycle (the lake,
`Estimating/OsinPocketLakeModel`).  At a joint inside the arc of `Π` or of `∂Δ` the outer sector is
a single corner, and a touch there breaks the inner cycle.  A walk touching itself at vertices of
both kinds breaks both cycles, so neither following hypothesis can be the residual.  Passages at a
vertex of the pocket walk do not interleave, so both sides are still discs.

* `IsNoncrossingClosedWalk.eulers_of_eitherFollows`: when one boundary cycle follows, both
  reclosings keep the Euler characteristic.  It covers the lake and the pinched two-gon.
* `PocketRegion.ofNoncrossingClosedWalkEuler`: the pocket region from the two Euler equalities.
* `PocketWalk.noncrossing_of_copyClean`: at least area, the walk of two exterior regions under the
  edge conditions is a noncrossing closed walk.
* `GloballyDistinguishedSectionFamily.exists_kept_of_noncrossingPocketWalk_of_eulers`: the kept
  cell from the two Euler equalities.
* `SectionPocketWalkEulerStatement` (not proved here) and `sectionPocketKeptCell_of_euler`:
  `SectionPocketKeptCellStatement` from the Euler equalities of the pocket walk.
* `osinSectionPocketFaceSetSection_of_regions_euler`: binder 6 from the `regions` stage and the Euler
  equalities.
* `OsinPocketKeptCellSection.lakeEulerBranch` (model test): on the lake map the inner cycle follows,
  the outer cycle does not, and both Euler equalities hold.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides Surgery.MapCollapse

namespace IsNoncrossingClosedWalk

variable {M : CombMap.{u}} {w : List M.Dart}

/-- **Both reclosings keep the Euler characteristic when one boundary cycle follows.** -/
theorem eulers_of_eitherFollows (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hfollow : (hw.outerCycle hM).FollowsBoundary ∨ (hw.innerCycle hM).FollowsBoundary) :
    (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).eulerCharacteristic =
        M.eulerCharacteristic ∧
      (reclosedMap M (sideOutside M w) (hw.outerCycle hM)).eulerCharacteristic =
        M.eulerCharacteristic := by
  rcases hfollow with hout | hin
  · exact ⟨hw.reclosed_euler hM hout,
      reclosedMap_euler_preserved M (sideOutside M w) (hw.outerCycle hM) hout hM⟩
  · exact ⟨reclosedMap_euler_preserved M (sideFaces M w) (hw.innerCycle hM) hin hM,
      hw.reclosed_euler_outer_of_innerFollows hM hin⟩

end IsNoncrossingClosedWalk

namespace PocketRegion

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} {walk : List Delta.toCombMap.Dart}

/-- **The pocket region of a noncrossing closed walk from the Euler equalities of its two
reclosings**: the faces on the walk's side, when the exterior face is on the other side.  Its
cycle is the walk, and its complement's cycle is the reversed walk.  No boundary cycle needs to
follow its boundary. -/
noncomputable def ofNoncrossingClosedWalkEuler (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hinner : (reclosedMap Delta.toCombMap (sideFaces Delta.toCombMap walk)
      (hw.innerCycle Delta.planar)).eulerCharacteristic = Delta.toCombMap.eulerCharacteristic)
    (houter : (reclosedMap Delta.toCombMap (sideOutside Delta.toCombMap walk)
      (hw.outerCycle Delta.planar)).eulerCharacteristic = Delta.toCombMap.eulerCharacteristic) :
    PocketRegion Delta where
  faces := sideFaces Delta.toCombMap walk
  outside := sideOutside Delta.toCombMap walk
  mem_outside_iff := mem_sideOutside_iff Delta.toCombMap walk
  outerFace_mem := (mem_sideOutside_iff Delta.toCombMap walk _).mpr hout
  inner := (hw.innerCycle Delta.planar).toDiscRegion_of_euler Delta.toCombMap _ Delta.planar.1
    hinner
  outer := (hw.outerCycle Delta.planar).toDiscRegion_of_euler Delta.toCombMap _ Delta.planar.1
    houter
  invDarts_outer_rotate := ⟨0, by
    rw [List.rotate_zero]
    exact invDarts_reverse_map_alpha walk⟩

theorem ofNoncrossingClosedWalkEuler_faces (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hinner : (reclosedMap Delta.toCombMap (sideFaces Delta.toCombMap walk)
      (hw.innerCycle Delta.planar)).eulerCharacteristic = Delta.toCombMap.eulerCharacteristic)
    (houter : (reclosedMap Delta.toCombMap (sideOutside Delta.toCombMap walk)
      (hw.outerCycle Delta.planar)).eulerCharacteristic = Delta.toCombMap.eulerCharacteristic) :
    (ofNoncrossingClosedWalkEuler hw hout hinner houter).faces =
      sideFaces Delta.toCombMap walk :=
  rfl

theorem ofNoncrossingClosedWalkEuler_inner_cycle
    (hw : IsNoncrossingClosedWalk Delta.toCombMap walk)
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap walk)
    (hinner : (reclosedMap Delta.toCombMap (sideFaces Delta.toCombMap walk)
      (hw.innerCycle Delta.planar)).eulerCharacteristic = Delta.toCombMap.eulerCharacteristic)
    (houter : (reclosedMap Delta.toCombMap (sideOutside Delta.toCombMap walk)
      (hw.outerCycle Delta.planar)).eulerCharacteristic = Delta.toCombMap.eulerCharacteristic) :
    (ofNoncrossingClosedWalkEuler hw hout hinner houter).inner.cycle = walk :=
  rfl

end PocketRegion

namespace PocketWalk

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The walk of two exterior regions under the edge conditions is noncrossing.**  At least area,
the walk of `exists_of_exteriorAt` has no repeated dart and no dart with its reverse, it is a closed
walk, and every two-colouring changing colour across it gives its darts one colour. -/
theorem noncrossing_of_copyClean (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hlea : S.diagram.LeastArea) {i : Fin S.diagram.rCellCount} {j : Fin cuts.count}
    {x y : RegionCandidate D eps S.diagram}
    (hx : x ∈ RegionCandidate.exteriorAt S.family i)
    (hy : y ∈ RegionCandidate.exteriorAt S.family i) (hxy : x ≠ y)
    (hjy : RegionCandidate.TargetsSectionIndex cuts j y)
    (K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ))
    (hKi : K.source = i) (hfirst : K.firstSide = y.2.leftSide)
    (hsecond : K.secondSide = x.2.rightSide)
    (hgap : ∃ Gap : CyclicArc (cellDarts S.diagram i),
      K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts)
    (hstart : K.targetArc.start.1 = x.2.targetArc.start.1)
    (hend : K.targetArc.start.1 + K.targetArc.length =
      y.2.targetArc.start.1 + y.2.targetArc.length)
    (hclean : K.CopyClean x y) :
    IsNoncrossingClosedWalk S.diagram.toCombMap K.walk := by
  obtain ⟨hxS, -, hxt⟩ := PocketWalkColour.mem_exteriorAt S.toRealizedSectionFamily hx
  obtain ⟨hyS, -, hyt⟩ := PocketWalkColour.mem_exteriorAt S.toRealizedSectionFamily hy
  obtain ⟨hxs, hxtgt⟩ := S.nondegenerate x hxS
  obtain ⟨hys, hytgt⟩ := S.nondegenerate y hyS
  have hyend : y.2.targetArc.start.1 + y.2.targetArc.length ≤ (outerDarts S.diagram).length :=
    Nat.le_trans hjy.2.2 (PocketWalk.cut_le_length_outerDarts S.toRealizedSectionFamily j.succ)
  obtain ⟨Gap, hsrc⟩ := hgap
  obtain ⟨hchain, hcloses⟩ := K.walk_isChain_closes x y hxt hyt hxs hys hxtgt hytgt hfirst hsecond
    Gap.darts hsrc hstart hend hyend
  obtain ⟨hnodup, halpha⟩ := K.walk_nodup_and_alpha_not_mem hlea hfirst hsecond
    (S.pairwise x hxS y hyS hxy) hclean
  exact ClosedWalkFaceColouring.isNoncrossingClosedWalk_of_orient S.diagram.planar K.walk_ne_nil
    hnodup halpha hchain
    (hcloses _ (Option.mem_def.mpr (List.getLast?_eq_some_getLast K.walk_ne_nil)) _
      (Option.mem_def.mpr (List.head?_eq_some_head K.walk_ne_nil)))
    (fun _ hcol => PocketWalkColour.walk_orient S.toRealizedSectionFamily hx hy hxy K hKi hfirst
      hsecond ⟨Gap, hsrc⟩ hstart hcol)

end PocketWalk

namespace GloballyDistinguishedSectionFamily

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The kept cell of a noncrossing pocket walk from the Euler equalities of its reclosings.**
Let `x ≠ y` be selected regions and `K` a pocket walk with the left side of `y`, the right side of
`x` and a source arc spanning the arcs of `x` and `y`.  If no relator word has value one, the walk
is noncrossing, the exterior face is off its side and both reclosings keep the Euler
characteristic, then a relator cell lies on the side of the walk. -/
theorem exists_kept_of_noncrossingPocketWalk_of_eulers
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {x y : RegionCandidate D eps S.diagram}
    (hxS : x ∈ S.family) (hyS : y ∈ S.family) (hxy : x ≠ y)
    (K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ))
    (hgap : ∃ Gap : CyclicArc (cellDarts S.diagram i),
      K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts)
    (hfirst : K.firstSide = y.2.leftSide) (hsecond : K.secondSide = x.2.rightSide)
    (hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1)
    (hw : IsNoncrossingClosedWalk S.diagram.toCombMap K.walk)
    (hout : S.diagram.outerFace ∉ sideFaces S.diagram.toCombMap K.walk)
    (hinner : (reclosedMap S.diagram.toCombMap (sideFaces S.diagram.toCombMap K.walk)
      (hw.innerCycle S.diagram.planar)).eulerCharacteristic =
        S.diagram.toCombMap.eulerCharacteristic)
    (houter : (reclosedMap S.diagram.toCombMap (sideOutside S.diagram.toCombMap K.walk)
      (hw.outerCycle S.diagram.planar)).eulerCharacteristic =
        S.diagram.toCombMap.eulerCharacteristic) :
    ∃ kept : Fin S.diagram.rCellCount,
      (cell S.diagram kept).face ∈ sideFaces S.diagram.toCombMap K.walk :=
  S.exists_kept_of_pocketRegion_of_value hxS hyS hxy K hgap hfirst hsecond hvalue
    (PocketRegion.ofNoncrossingClosedWalkEuler hw hout hinner houter) rfl

end GloballyDistinguishedSectionFamily

/-- **The Euler equalities of the pocket walk** (not proved here; option (iv) of the lake).  On a
least-area diagram, the pocket walk `s_1 t_1 s_2 t_2` of two distinct exterior regions of one cell
to one section, in the shape of `PocketWalk.exists_of_exteriorAt` and satisfying the edge
conditions, is noncrossing, and both of its reclosings keep the Euler characteristic of the map. -/
def SectionPocketWalkEulerStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    S.diagram.LeastArea →
      ∀ (i : Fin S.diagram.rCellCount) (j : Fin cuts.count)
        (x y : RegionCandidate D eps S.diagram),
        x ∈ RegionCandidate.exteriorAt S.family i → y ∈ RegionCandidate.exteriorAt S.family i →
          x ≠ y → RegionCandidate.TargetsSectionIndex cuts j x →
            RegionCandidate.TargetsSectionIndex cuts j y →
              ∀ K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ),
                K.source = i → K.firstSide = y.2.leftSide → K.secondSide = x.2.rightSide →
                  (∃ Gap : CyclicArc (cellDarts S.diagram i),
                    K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++
                      y.2.sourceArc.darts) →
                    K.targetArc.start.1 = x.2.targetArc.start.1 →
                      K.targetArc.start.1 + K.targetArc.length =
                          y.2.targetArc.start.1 + y.2.targetArc.length →
                        K.CopyClean x y →
                          ∀ hw : IsNoncrossingClosedWalk S.diagram.toCombMap K.walk,
                            (reclosedMap S.diagram.toCombMap
                                (sideFaces S.diagram.toCombMap K.walk)
                                (hw.innerCycle S.diagram.planar)).eulerCharacteristic =
                                S.diagram.toCombMap.eulerCharacteristic ∧
                              (reclosedMap S.diagram.toCombMap
                                  (sideOutside S.diagram.toCombMap K.walk)
                                  (hw.outerCycle S.diagram.planar)).eulerCharacteristic =
                                S.diagram.toCombMap.eulerCharacteristic

/-- **The kept cell of the pocket, from the Euler equalities of the pocket walk.** -/
theorem sectionPocketKeptCell_of_euler (heuler : SectionPocketWalkEulerStatement.{u, w, v}) :
    SectionPocketKeptCellStatement.{u, w, v} := by
  unfold SectionPocketKeptCellStatement
  intro _ _ _ D lambda c eps W Delta cuts S hlea i j x y hx hy hxy hjx hjy K hKi hfirst hsecond
    hgap hstart hend hclean
  have hw := PocketWalk.noncrossing_of_copyClean S hlea hx hy hxy hjy K hKi hfirst hsecond hgap
    hstart hend hclean
  obtain ⟨hinner, houter⟩ := heuler D lambda c eps W Delta cuts S hlea i j x y hx hy hxy hjx hjy K
    hKi hfirst hsecond hgap hstart hend hclean hw
  obtain ⟨hxS, -, -⟩ := PocketWalkColour.mem_exteriorAt S.toRealizedSectionFamily hx
  obtain ⟨hyS, -, -⟩ := PocketWalkColour.mem_exteriorAt S.toRealizedSectionFamily hy
  exact S.exists_kept_of_noncrossingPocketWalk_of_eulers hxS hyS hxy K hgap hfirst hsecond
    (fun C hC => DiscDiagram.leastArea_listVal_word_ne_one hlea C hC) hw
    (K.outerFace_not_mem_sideFaces_of_noncrossing hw) hinner houter

/-- **Binder 6 from the `regions` stage and the Euler equalities of the pocket walk.** -/
theorem osinSectionPocketFaceSetSection_of_regions_euler
    (hregions : SectionPocketRegionsCopyStatement.{u, w, v})
    (heuler : SectionPocketWalkEulerStatement.{u, w, v}) :
    OsinSectionPocketFaceSetSectionStatement.{u, w, v} :=
  osinSectionPocketFaceSetSection_of_residuals hregions (sectionPocketKeptCell_of_euler heuler)

namespace OsinPocketKeptCellSection

/-- **The lake under the Euler builder** (model test).  On the lake map of `OsinPocketLakeModel`,
the walk `[0,2]` passes twice through its vertex, its outer cycle does not follow its boundary, and
both reclosings keep the Euler characteristic, through the inner cycle. -/
def LakeEulerBranch : Prop :=
  (reclosedMap OsinPocketLakeModel.M (sideFaces OsinPocketLakeModel.M ([0, 2] : List (Fin 4)))
      (OsinPocketLakeModel.isNoncrossingClosedWalk_lakeCycle.innerCycle
        OsinPocketLakeModel.planar)).eulerCharacteristic =
      OsinPocketLakeModel.M.eulerCharacteristic ∧
    (reclosedMap OsinPocketLakeModel.M (sideOutside OsinPocketLakeModel.M ([0, 2] : List (Fin 4)))
      (OsinPocketLakeModel.isNoncrossingClosedWalk_lakeCycle.outerCycle
        OsinPocketLakeModel.planar)).eulerCharacteristic =
      OsinPocketLakeModel.M.eulerCharacteristic ∧
    ¬ (OsinPocketLakeModel.isNoncrossingClosedWalk_lakeCycle.outerCycle
      OsinPocketLakeModel.planar).FollowsBoundary

theorem lakeEulerBranch : LakeEulerBranch := by
  obtain ⟨h1, h2⟩ := OsinPocketLakeModel.isNoncrossingClosedWalk_lakeCycle.eulers_of_eitherFollows
    OsinPocketLakeModel.planar (Or.inr OsinPocketLakeModel.lakeCycle_innerCycle_followsBoundary)
  exact ⟨h1, h2, OsinPocketLakeModel.lakeCycle_outerCycle_not_followsBoundary⟩

end OsinPocketKeptCellSection

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.eulers_of_eitherFollows
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.ofNoncrossingClosedWalkEuler
#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.noncrossing_of_copyClean
#audit_axioms
  GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.exists_kept_of_noncrossingPocketWalk_of_eulers
#audit_axioms GroupApproximation.GGT.VanKampen.SectionPocketWalkEulerStatement
#audit_axioms GroupApproximation.GGT.VanKampen.sectionPocketKeptCell_of_euler
#audit_axioms GroupApproximation.GGT.VanKampen.osinSectionPocketFaceSetSection_of_regions_euler
#audit_closed_axioms GroupApproximation.GGT.VanKampen.OsinPocketKeptCellSection.lakeEulerBranch
