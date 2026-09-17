import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.RemoveRegion
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFaceSetOnCopy
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketKeptCellSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketKeptCellNoncrossing
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkEulerSectorFree
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkNoninterleavingJoints
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkColour
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCopyWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLakeAbsorption
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52Prep
import GroupApproximation.GGT.VanKampen.Estimating.RegionProfileTransport
import GroupApproximation.GGT.VanKampen.SurgeryRegionPairThickeningRegions
import GroupApproximation.GGT.VanKampen.SurgeryOuterCellThickening
import GroupApproximation.Meta.AxiomGuard

/-!
# A proper source arc for the section pocket

Assembly of `OsinSectionPocketFaceSetProperSectionStatement` (the mathematical proof is in the
docstring of `P08ProperArc.ArcSplit`).  On the copy-clean copy, the pocket walk of two ordered
exterior regions `x`, `y` of one cell to one section is noncrossing with a kept relator cell on its
side.  Removing the region `y` from that side gives a pocket face set with boundary cycle
`yR⁻¹ ++ T'⁻¹ ++ xR ++ t₂`, a closed walk, whose source arc `T' = xA ++ Gap` misses the nonempty
source arc `yA`, so it is proper.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc

universe u w v

open Embedded SimpleClosedWalkSides SameCellPocketWalk
open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w}

section Diagram

variable {W : Set (List (RelLetter G Lambda))} {X : DiscDiagram.{u, w, v} W}

/-- Step 4: **no dart of `y`'s right side is kept by the pocket walk.** -/
theorem right_not_walkKeep {D : RelGenSet G Lambda} {eps lo hi : ℕ}
    (K : PocketWalk D eps X lo hi) {x y : RegionCandidate D eps X} (hlea : X.LeastArea)
    (hfirst : K.firstSide = y.2.leftSide) (hsecond : K.secondSide = x.2.rightSide)
    (hdisj : Disjoint x.1 y.1) (hclean : K.CopyClean x y) (hclean' : K.CopyClean y x)
    {Yd : List X.toCombMap.Dart}
    (hyn : (invDarts X y.2.sourceArc.darts ++ y.2.rightSide ++ Yd ++ y.2.leftSide).Nodup) :
    ∀ e ∈ y.2.rightSide, ¬ walkKeep X.toCombMap K.walk e := by
  have avoid : (cell X K.source).face ∉ y.1 :=
    (y.2.innerGRegion hlea).cells_avoid (cell X K.source) (cell_mem X K.source)
  intro e he hk
  obtain ⟨hey, hαy⟩ := PocketWalk.mem_rightSide_boundary y he
  rcases hk with hw | hw
  · rcases K.mem_walk_cases hw with h | h | h | h
    · rw [hfirst] at h
      exact (not_mem_of_nodup_snd hyn he).2.2 h
    · exact hclean'.side_cell e (List.mem_append_right _ he)
        (K.faceOf_alpha_of_mem_invDarts_sourceArc h)
    · rw [hsecond] at h
      exact Finset.disjoint_left.mp hdisj (PocketWalk.mem_rightSide_boundary x h).1 hey
    · exact hclean'.side_outer e (List.mem_append_right _ he) (K.faceOf_alpha_of_mem_targetArc h)
  · rcases K.mem_walk_cases hw with h | h | h | h
    · rw [hfirst] at h
      exact hαy (PocketWalk.mem_leftSide_boundary y h).1
    · have hc := K.faceOf_alpha_of_mem_invDarts_sourceArc h
      rw [X.toCombMap.alpha_involutive e] at hc
      rw [hc] at hey
      exact avoid hey
    · rw [hsecond] at h
      have hr := hclean.regions _ (PocketWalk.mem_rightSide_boundary x h).1
      rw [X.toCombMap.alpha_involutive e] at hr
      exact hr hey
    · have hc := K.faceOf_alpha_of_mem_targetArc h
      rw [X.toCombMap.alpha_involutive e] at hc
      exact (y.2.boundary.all_gCells _ hey).1 hc

/-- Steps 5–7: **removing the region `y` from the side of the walk** gives a proper pocket face set
in walk order. -/
theorem exists_pocketFaceSet_of_split {D : RelGenSet G Lambda} {eps lo hi : ℕ}
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    {w : List X.toCombMap.Dart} (hw : IsNoncrossingClosedWalk X.toCombMap w)
    (y : RegionCandidate D eps X) (source : Fin X.rCellCount)
    (T' : CyclicArc (cellDarts X source)) (t₂ : CyclicArc (outerDarts X))
    (xR A Yd : List X.toCombMap.Dart)
    (hwalk : w = y.2.leftSide ++ invDarts X A ++ (invDarts X T'.darts ++ xR ++ t₂.darts) ++ Yd)
    (hcyc : y.2.boundary.cycle = invDarts X A ++ y.2.rightSide ++ Yd ++ y.2.leftSide)
    (hInt : ∀ t, X.toCombMap.faceOf t ∈ y.1 → X.toCombMap.faceOf (X.toCombMap.alpha t) ∈ y.1 →
      ¬ walkKeep X.toCombMap w t)
    (hR : ∀ e ∈ y.2.rightSide, ¬ walkKeep X.toCombMap w e)
    (hA : A ≠ []) (hYd : Yd ≠ []) (hT' : T'.darts ≠ []) (hxR : xR.length ≤ eps)
    (kept : Fin X.rCellCount) (hkF : (cell X kept).face ∈ sideFaces X.toCombMap w)
    (hky : (cell X kept).face ∉ y.1)
    (hsrc : (cell X source).face ∉ sideFaces X.toCombMap w)
    (hout : X.outerFace ∉ sideFaces X.toCombMap w)
    (hlo : lo ≤ t₂.start.1) (hhi : t₂.start.1 + t₂.length ≤ hi)
    (hprop : T'.length < (cellDarts X source).length) :
    ∃ P : PocketFaceSet D eps X lo hi,
      P.ClosedWalk ∧ P.sourceArc.length < (cellDarts X P.source).length := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil T'.darts hT'
  have hinvT' : invDarts X T'.darts ≠ [] :=
    List.ne_nil_of_mem (List.mem_map_of_mem (f := X.toCombMap.alpha) (List.mem_reverse.mpr ha))
  have hMid : invDarts X T'.darts ++ xR ++ t₂.darts ≠ [] :=
    List.append_ne_nil_of_left_ne_nil (List.append_ne_nil_of_left_ne_nil hinvT' _) _
  obtain ⟨d₀, hd₀⟩ := List.exists_mem_of_ne_nil Yd hYd
  have hd₀w : d₀ ∈ w := by rw [hwalk]; exact mem4_4 hd₀
  have hd₀c : d₀ ∈ y.2.boundary.cycle := by rw [hcyc]; exact mem4_3 hd₀
  have hcycF := cycle_faces_mem hw y.2.boundary hInt hd₀w hd₀c
  have hmem : ∀ d, d ∈ invDarts X y.2.rightSide ++ (invDarts X T'.darts ++ xR ++ t₂.darts) ↔
      Surgery.MapCollapse.IsBoundaryDart X.toCombMap (sideFaces X.toCombMap w \ y.1) d :=
    fun d => ⟨isBoundaryDart_sdiff_of_mem hw y.2.boundary hwalk hcyc hInt hR hcycF d,
      mem_of_isBoundaryDart_sdiff hw y.2.boundary hwalk hcyc d⟩
  have hre : invDarts X y.2.rightSide ++ invDarts X T'.darts ++ xR ++ t₂.darts =
      invDarts X y.2.rightSide ++ (invDarts X T'.darts ++ xR ++ t₂.darts) := by
    simp only [List.append_assoc]
  have hfl : (invDarts X y.2.rightSide).length ≤ eps := by
    simpa only [invDarts, List.length_map, List.length_reverse] using y.2.rightSide_length_le
  refine ⟨{ faces := sideFaces X.toCombMap w \ y.1
            outerFace_not_mem := fun h => hout (Finset.mem_sdiff.mp h).1
            source := source
            source_not_mem := fun h => hsrc (Finset.mem_sdiff.mp h).1
            kept := kept
            kept_mem := Finset.mem_sdiff.mpr ⟨hkF, hky⟩
            sourceArc := T'
            targetArc := t₂
            firstSide := invDarts X y.2.rightSide
            secondSide := xR
            boundary :=
              { cycle := invDarts X y.2.rightSide ++ invDarts X T'.darts ++ xR ++ t₂.darts
                cycle_nonempty := by
                  rw [hre]
                  exact List.append_ne_nil_of_right_ne_nil _ hMid
                cycle_nodup := by
                  rw [hre]
                  exact newCycle_nodup hw y.2.boundary hwalk hcyc hR
                cycle_mem_iff := fun d => by
                  rw [hre]
                  exact hmem d }
            decomposition := rfl
            firstSide_length_le := hfl
            secondSide_length_le := hxR
            firstSide_norm_le := (PocketFaceSet.wordNorm_dartWord_le_length hlabel _).trans hfl
            secondSide_norm_le := (PocketFaceSet.wordNorm_dartWord_le_length hlabel _).trans hxR
            lo_le := hlo
            le_hi := hhi }, ?_, hprop⟩
  apply closedWalk_of_isClosedDartWalk
  show IsClosedDartWalk X.toCombMap
    (invDarts X y.2.rightSide ++ invDarts X T'.darts ++ xR ++ t₂.darts)
  rw [hre]
  exact newCycle_closed hw y.2.boundary hwalk hcyc hA hYd hMid

/-- Step 2: **splitting the source and target arcs** of the pocket walk at the region `y`. -/
theorem exists_split_arcs {D : RelGenSet G Lambda} {eps lo hi : ℕ}
    (K : PocketWalk D eps X lo hi) {x y : RegionCandidate D eps X}
    (hfirst : K.firstSide = y.2.leftSide) (hsecond : K.secondSide = x.2.rightSide)
    {Gap : List X.toCombMap.Dart}
    (hsrc : K.sourceArc.darts = x.2.sourceArc.darts ++ Gap ++ y.2.sourceArc.darts)
    (hyt : y.2.target = none) (hstart_le : K.targetArc.start.1 ≤ y.2.targetArc.start.1)
    (hend : K.targetArc.start.1 + K.targetArc.length =
      y.2.targetArc.start.1 + y.2.targetArc.length)
    (hn : K.targetArc.start.1 + K.targetArc.length ≤ (outerDarts X).length) :
    ∃ (T' : CyclicArc (cellDarts X K.source)) (t₂ : CyclicArc (outerDarts X)),
      T'.length + y.2.sourceArc.length = K.sourceArc.length ∧
        T'.darts = x.2.sourceArc.darts ++ Gap ∧ t₂.start = K.targetArc.start ∧
          t₂.start.1 + t₂.length = y.2.targetArc.start.1 ∧
            K.walk = y.2.leftSide ++ invDarts X y.2.sourceArc.darts ++
              (invDarts X T'.darts ++ x.2.rightSide ++ t₂.darts) ++ y.2.targetArc.darts := by
  obtain ⟨T', -, hT'l, hT'd⟩ := exists_prefix K.sourceArc hsrc
  obtain ⟨Yt, hYs, hYl, hYd⟩ : ∃ arc' : CyclicArc (outerDarts X),
      arc'.start.1 = y.2.targetArc.start.1 ∧ arc'.length = y.2.targetArc.length ∧
        arc'.darts = y.2.targetArc.darts :=
    CyclicArc.exists_transport (targetDarts X) hyt y.2.targetArc
  obtain ⟨t₂, ht₂s, ht₂e, ht₂d⟩ :=
    exists_prefix_of_suffix K.targetArc Yt (by omega) (by omega) hn
  refine ⟨T', t₂, by rw [← y.2.sourceArc.darts_length]; exact hT'l, hT'd, ht₂s, by omega, ?_⟩
  show K.firstSide ++ invDarts X K.sourceArc.darts ++ K.secondSide ++ K.targetArc.darts = _
  rw [hfirst, hsecond, hsrc, ← hT'd, ht₂d, hYd]
  simp only [invDarts, List.reverse_append, List.map_append, List.append_assoc]

end Diagram

section Sections

variable {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {lambda c : ℝ}
  {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- The source cell of a pocket walk is not on the side of the walk. -/
theorem source_not_mem_sideFaces {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}
    (K : PocketWalk D eps X lo hi) (hw : IsNoncrossingClosedWalk X.toCombMap K.walk) :
    (cell X K.source).face ∉ sideFaces X.toCombMap K.walk := by
  obtain ⟨d, hd⟩ := K.sourceArc.exists_mem_darts K.sourceArc_pos
  have hinv : X.toCombMap.alpha d ∈ invDarts X K.sourceArc.darts :=
    List.mem_map_of_mem (f := X.toCombMap.alpha) (List.mem_reverse.mpr hd)
  have hdw : X.toCombMap.alpha d ∈ K.walk := by
    show _ ∈ K.firstSide ++ invDarts X K.sourceArc.darts ++ K.secondSide ++ K.targetArc.darts
    exact mem4_2 hinv
  have hface : X.toCombMap.faceOf d = (cell X K.source).face :=
    ((X.faceBoundary (cell X K.source).face).mem_iff d).mp (K.sourceArc.mem_cycle_of_mem_darts hd)
  have h := And.right ((hw.isBoundaryDart_sideFaces_iff X.planar _).mpr hdw)
  rwa [X.toCombMap.alpha_involutive d, hface] at h

/-- **The proper pocket face set of two ordered exterior regions**, on a copy-clean family. -/
theorem exists_proper_of_le (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (hlea : S.diagram.LeastArea) {i : Fin S.diagram.rCellCount} {j : Fin cuts.count}
    {x y : RegionCandidate D eps S.diagram}
    (hx : x ∈ RegionCandidate.exteriorAt S.family i)
    (hy : y ∈ RegionCandidate.exteriorAt S.family i) (hxy : x ≠ y)
    (hjx : RegionCandidate.TargetsSectionIndex cuts j x)
    (hjy : RegionCandidate.TargetsSectionIndex cuts j y)
    (hle : x.2.targetArc.start.1 ≤ y.2.targetArc.start.1)
    (hcl : ∀ (x y : RegionCandidate D eps S.diagram), x ∈ RegionCandidate.exteriorAt S.family i →
      y ∈ RegionCandidate.exteriorAt S.family i → x ≠ y →
        ∀ (lo hi : ℕ) (K : PocketWalk D eps S.diagram lo hi), K.source = i → K.CopyClean x y) :
    ∃ P : PocketFaceSet D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ),
      P.ClosedWalk ∧ P.sourceArc.length < (cellDarts S.diagram P.source).length := by
  obtain ⟨K, hKi, hfirst, hsecond, ⟨Gap, hsrc⟩, hstart, hend⟩ :=
    PocketWalk.exists_of_le S.toRealizedSectionFamily hx hy hxy hjx hjy hle
  have hclean : K.CopyClean x y := hcl x y hx hy hxy _ _ K hKi
  have hclean' : K.CopyClean y x := hcl y x hy hx hxy.symm _ _ K hKi
  have hw := PocketWalk.noncrossing_of_copyClean S hlea hx hy hxy hjy K hKi hfirst hsecond
    ⟨Gap, hsrc⟩ hstart hend hclean
  obtain ⟨kept, hkF⟩ := sectionPocketKeptCell D lambda c eps W Delta cuts S hlea i j x y hx hy hxy
    hjx hjy K hKi hfirst hsecond ⟨Gap, hsrc⟩ hstart hend hclean
  obtain ⟨hxS, -, -⟩ := PocketWalkColour.mem_exteriorAt S.toRealizedSectionFamily hx
  obtain ⟨hyS, -, hyt⟩ := PocketWalkColour.mem_exteriorAt S.toRealizedSectionFamily hy
  have hdisj : Disjoint x.1 y.1 := S.pairwise x hxS y hyS hxy
  have hn := K.le_hi.trans (PocketWalk.cut_le_length_outerDarts S.toRealizedSectionFamily j.succ)
  obtain ⟨T', t₂, hT'l, hT'd, ht₂s, ht₂e, hwalk⟩ :=
    exists_split_arcs K hfirst hsecond hsrc hyt (by omega) hend hn
  have hcyc : y.2.boundary.cycle =
      invDarts S.diagram y.2.sourceArc.darts ++ y.2.rightSide ++ y.2.targetArc.darts ++
        y.2.leftSide := by
    have h := y.2.boundary_decomposition
    rw [targetBoundaryDarts_none _ hyt] at h
    exact h
  have hyn : (invDarts S.diagram y.2.sourceArc.darts ++ y.2.rightSide ++ y.2.targetArc.darts ++
      y.2.leftSide).Nodup := by
    rw [← hcyc]; exact y.2.boundary.cycle_nodup
  have hR := right_not_walkKeep K hlea hfirst hsecond hdisj hclean hclean' hyn
  have hInt := (K.internal_not_walkKeep hlea hfirst hsecond hdisj).2
  obtain ⟨hxs, -⟩ := S.nondegenerate x hxS
  obtain ⟨hys, hyT⟩ := S.nondegenerate y hyS
  have hA : y.2.sourceArc.darts ≠ [] :=
    List.ne_nil_of_length_pos (by rw [y.2.sourceArc.darts_length]; exact hys)
  have hYd : y.2.targetArc.darts ≠ [] :=
    List.ne_nil_of_length_pos (by rw [y.2.targetArc.darts_length]; exact hyT)
  have hT' : T'.darts ≠ [] := by
    rw [hT'd]
    exact List.append_ne_nil_of_left_ne_nil
      (List.ne_nil_of_length_pos (by rw [x.2.sourceArc.darts_length]; exact hxs)) _
  have hky : (cell S.diagram kept).face ∉ y.1 :=
    (y.2.innerGRegion hlea).cells_avoid (cell S.diagram kept) (cell_mem S.diagram kept)
  have hlo : cuts.cut j.castSucc ≤ t₂.start.1 := by rw [ht₂s]; exact K.lo_le
  obtain ⟨-, -, hyhi⟩ := hjy
  have hhi : t₂.start.1 + t₂.length ≤ cuts.cut j.succ := by omega
  have hprop : T'.length < (cellDarts S.diagram K.source).length := by
    have := K.sourceArc.length_le
    omega
  exact exists_pocketFaceSet_of_split S.label_admissible hw y K.source T' t₂ x.2.rightSide
    y.2.sourceArc.darts y.2.targetArc.darts hwalk hcyc hInt hR hA hYd hT'
    x.2.rightSide_length_le kept hkF hky (source_not_mem_sideFaces K hw)
    (K.outerFace_not_mem_sideFaces_of_noncrossing hw) hlo hhi hprop

end Sections

/-- **The proper face set producer** at fixed parameters. -/
theorem input (D : RelGenSet G Lambda) (lambda c : ℝ)
    (eps : ℕ) (W : Set (List (RelLetter G Lambda))) :
    SectionPocketFaceSetProperInput.{u, w, v} D lambda c eps W := by
  unfold SectionPocketFaceSetProperInput
  intro Delta cuts hlea S i j a ha b hb hab hja hjb
  have haS : a ∈ S.family := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
  have hbS : b ∈ S.family := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1
  have hlen0 := PocketFaceSetOnCopy.one_lt_boundaryWord_length S haS hbS hab hja.1 hjb.1
  obtain ⟨S₄, e, ⟨E⟩, hp, hcl⟩ :=
    PocketFaceSetOnCopy.exists_copyClean RegionPairThickening.sectionPocketRegionsCopy hlea S hlen0
  obtain ⟨i', a', b', -, ha', hb', hab', hja', hjb'⟩ :=
    RegionProfileTransport.exists_exteriorPair e hp ha hb hab hja hjb
  have hlea₄ : S₄.diagram.LeastArea := OuterCellThickening.leastArea_of_oEquivalent S₄.equiv hlea
  refine ⟨S₄.diagram, ⟨E⟩, S₄.label_admissible, ?_⟩
  rcases le_total a'.2.targetArc.start.1 b'.2.targetArc.start.1 with hle | hle
  · exact exists_proper_of_le S₄ hlea₄ ha' hb' hab' hja' hjb' hle (hcl i')
  · exact exists_proper_of_le S₄ hlea₄ hb' ha' hab'.symm hjb' hja' hle (hcl i')

/-- **`OsinSectionPocketFaceSetProperSectionStatement`**, unconditionally, with `ε₀ = 0` and
`ρ₀ = 1`. -/
theorem proof : OsinSectionPocketFaceSetProperSectionStatement.{u, w, v} := by
  unfold OsinSectionPocketFaceSetProperSectionStatement
  intro G _ Lambda D _ lambda c _ _ _ _ _ _
  exact ⟨0, fun eps _ => ⟨1, Nat.one_pos, fun _ _ W _ => input D lambda c eps W⟩⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P08ProperArc.proof
