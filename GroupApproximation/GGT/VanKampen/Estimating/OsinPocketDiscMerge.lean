import GroupApproximation.GGT.VanKampen.SurgeryInnerDiscCollapseRegions
import GroupApproximation.GGT.VanKampen.SurgeryInnerDiscCollapseMerged
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMergeRegion
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixCutMerge
import GroupApproximation.Meta.AxiomGuard

/-!
# Merging a pocket through its disc region

`Estimating/OsinAppendixCutMerge.lean` refutes a collapse of G-cells absorbing at least two
selected regions into one contiguity region (`false_of_collapse_singleton`), for a region with an
embedded boundary (`Surgery.InnerGRegion`).  A pocket whose two contiguity regions meet at one
vertex has a disc region (`PocketRegion.inner`) but no embedded boundary.  This file runs the same
argument through `Surgery.InnerDiscRegion` (`SurgeryInnerDiscCollapse.lean`), which needs only the
disc region:

* `Surgery.InnerDiscRegion.ofPocketRegion`: a pocket holding no relator cell is a collapsible disc
  region, with the value of `PocketRegion.listVal_inner_eq_one`;
* `Surgery.InnerDiscRegion.regionFamily_profile` and `regionFamily_avoid_merged`: the regions
  avoiding the collapsed faces keep their target profile and miss the merged face;
* `Surgery.InnerDiscRegion.mergedGeometry`: if the cycle of the disc region, started at some dart,
  reads a reversed source arc, a side, a target arc and a side, then the merged face of the
  collapse is one contiguity region (`ContiguityGeometry.ofSingletonFace`) with the transported
  arcs and sides;
* `GloballyDistinguishedSectionFamily.false_of_disc_collapse_singleton`: the contradiction of
  `false_of_collapse_singleton`, for a disc region.

Infrastructure for Osin's Lemma 9.7(a) (arXiv:math/0411039v3); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen.Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace Surgery.InnerDiscRegion

variable {Delta : DiscDiagram.{u, w, v} W}

/-- **A pocket as a collapsible disc region.**  A pocket region holding no relator cell is a disc
region avoiding the exterior, and its cycle reads a trivial element. -/
def ofPocketRegion (P : PocketRegion Delta)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces) : InnerDiscRegion Delta where
  faces := P.faces
  region := P.inner
  outer_not_mem := P.outerFace_not_mem
  cells_avoid := hcells
  value_one := P.listVal_inner_eq_one hcells

theorem ofPocketRegion_faces (P : PocketRegion Delta)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces) :
    (ofPocketRegion P hcells).faces = P.faces :=
  rfl

theorem ofPocketRegion_region_cycle (P : PocketRegion Delta)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces) :
    (ofPocketRegion P hcells).region.cycle = P.inner.cycle :=
  rfl

variable (R : InnerDiscRegion Delta)

/-! ## Regions carried through the collapse -/

/-- Every region of a family carried through the collapse has the target profile of the
region it came from. -/
theorem regionFamily_profile {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Disjoint a.1 R.faces) {a : RegionCandidate D eps R.diagram}
    (ha : a ∈ R.regionFamily family havoid) :
    ∃ b ∈ family, RegionCandidate.SameTargetProfile a b := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  refine ⟨b.val, b.property, And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))⟩
  · exact Option.map_eq_none_iff
  · exact CyclicArc.mapTo_start b.val.2.targetArc R.keep (R.targetDarts_eq b.val.2.target)
  · exact CyclicArc.mapTo_length b.val.2.targetArc R.keep (R.targetDarts_eq b.val.2.target)
  · exact CyclicArc.mapTo_length b.val.2.sourceArc R.keep (R.cellDarts_eq b.val.2.source)

/-- No region of a family carried through the collapse is a loop if none of the family is. -/
theorem regionFamily_noLoop {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Disjoint a.1 R.faces)
    (hfamily : ∀ b ∈ family, b.2.target ≠ some b.2.source)
    {a : RegionCandidate D eps R.diagram} (ha : a ∈ R.regionFamily family havoid) :
    a.2.target ≠ some a.2.source := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  intro h
  change Option.map R.cellMap.indexEquiv b.val.2.target =
    some (R.cellMap.indexEquiv b.val.2.source) at h
  exact hfamily b.val b.property (Option.map_injective R.cellMap.indexEquiv.injective h)

/-- No region of a family carried through the collapse contains the merged face. -/
theorem regionFamily_avoid_merged {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Disjoint a.1 R.faces) :
    ∀ a ∈ R.regionFamily family havoid, R.merged ∉ a.1 := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := R.regionFamily_faces family havoid ha
  rw [hab]
  exact R.merged_not_mem_faceSet (havoid b hb)

/-! ## The merged face -/

/-- No dart of the cycle of the disc region is internal. -/
theorem cycle_not_internal {d : Delta.toCombMap.Dart} (hd : d ∈ R.region.cycle) :
    ¬ MapCollapse.InternalDart Delta.toCombMap R.faces d :=
  R.not_internal_of_faceOf_alpha_not_mem ((R.region.cycle_mem_iff d).mp hd).2

/-- The sides of a decomposition of the rotated cycle have no internal dart. -/
theorem sides_not_internal {k : ℕ} {l₁ l₂ l₃ l₄ : List Delta.toCombMap.Dart}
    (hdecomp : R.region.cycle.rotate k = l₁ ++ l₂ ++ l₃ ++ l₄) :
    (∀ d ∈ l₂, ¬ MapCollapse.InternalDart Delta.toCombMap R.faces d) ∧
      ∀ d ∈ l₄, ¬ MapCollapse.InternalDart Delta.toCombMap R.faces d := by
  have hmem : ∀ d ∈ l₁ ++ l₂ ++ l₃ ++ l₄,
      ¬ MapCollapse.InternalDart Delta.toCombMap R.faces d := by
    intro d hd
    rw [← hdecomp] at hd
    exact R.cycle_not_internal (List.mem_rotate.mp hd)
  exact ⟨fun d hd => hmem d (by simp [hd]), fun d hd => hmem d (by simp [hd])⟩

/-- **The merged face lists the cycle of the disc region.** -/
theorem faceBoundary_merged_darts_eq_map_keep :
    (R.diagram.faceBoundary R.merged).darts = R.region.cycle.map R.keep := by
  apply List.map_injective_iff.mpr R.val_injective
  rw [R.faceBoundary_merged_map_val, R.map_keep_val fun d hd => R.cycle_not_internal hd]

/-- **A decomposition of the rotated cycle decomposes the merged face.** -/
theorem faceBoundary_merged_rotate {k : ℕ} {source : Fin Delta.rCellCount}
    {target : Option (Fin Delta.rCellCount)} (sourceArc : CyclicArc (cellDarts Delta source))
    (targetArc : CyclicArc (targetDarts Delta target))
    {rightSide leftSide : List Delta.toCombMap.Dart}
    (hdecomp : R.region.cycle.rotate k =
      sourceArc.reverseDarts ++ rightSide ++ targetBoundaryDarts Delta target targetArc ++
        leftSide) :
    (R.diagram.faceBoundary R.merged).darts.rotate k =
      (sourceArc.mapTo R.keep (R.cellDarts_eq source)).reverseDarts ++ rightSide.map R.keep ++
        targetBoundaryDarts R.diagram (target.map R.cellMap.indexEquiv)
          (targetArc.mapTo R.keep (R.targetDarts_eq target)) ++ leftSide.map R.keep := by
  rw [R.faceBoundary_merged_darts_eq_map_keep, ← List.map_rotate, hdecomp,
    R.reverseDarts_mapTo (fun d hd => R.cellDarts_not_internal source hd) sourceArc
      (R.cellDarts_eq source),
    R.targetBoundaryDarts_map target targetArc]
  simp only [List.map_append]

section Merged

variable {D : RelGenSet G Lambda} {eps : ℕ} {k : ℕ} {source : Fin Delta.rCellCount}
  {target : Option (Fin Delta.rCellCount)} (sourceArc : CyclicArc (cellDarts Delta source))
  (targetArc : CyclicArc (targetDarts Delta target))
  {rightSide leftSide : List Delta.toCombMap.Dart}
  (hdecomp : R.region.cycle.rotate k =
    sourceArc.reverseDarts ++ rightSide ++ targetBoundaryDarts Delta target targetArc ++ leftSide)
  (hright : rightSide.length ≤ eps) (hleft : leftSide.length ≤ eps)
  (hrightNorm : WordMetric.wordNorm D.alphabet.carrier
    (RelLetter.listVal (dartWord Delta rightSide)) ≤ eps)
  (hleftNorm : WordMetric.wordNorm D.alphabet.carrier
    (RelLetter.listVal (dartWord Delta leftSide)) ≤ eps)

/-- **The merged face as one contiguity region.**  If the cycle of the disc region, started at
some dart, is a reversed arc of a relator cell, a side, an arc of the target and a side, then the
merged face is a contiguity region with the transported arcs and sides. -/
noncomputable def mergedGeometry :
    ContiguityGeometry D eps R.diagram ({R.merged} : Finset R.diagram.toCombMap.Face) :=
  ContiguityGeometry.ofSingletonFace R.merged R.merged_ne_outer R.merged_value
    R.merged_noInternalFaceDart k (R.cellMap.indexEquiv source)
    (target.map R.cellMap.indexEquiv) (sourceArc.mapTo R.keep (R.cellDarts_eq source))
    (targetArc.mapTo R.keep (R.targetDarts_eq target)) (rightSide.map R.keep)
    (leftSide.map R.keep) (R.faceBoundary_merged_rotate sourceArc targetArc hdecomp)
    (by rw [List.length_map]; exact hright) (by rw [List.length_map]; exact hleft)
    (by rw [R.dartWord_map (R.sides_not_internal hdecomp).1]; exact hrightNorm)
    (by rw [R.dartWord_map (R.sides_not_internal hdecomp).2]; exact hleftNorm)

theorem mergedGeometry_target :
    (R.mergedGeometry sourceArc targetArc hdecomp hright hleft hrightNorm
      hleftNorm).target = target.map R.cellMap.indexEquiv :=
  rfl

theorem mergedGeometry_sourceArc_length :
    (R.mergedGeometry sourceArc targetArc hdecomp hright hleft hrightNorm
      hleftNorm).sourceArc.length = sourceArc.length :=
  sourceArc.mapTo_length R.keep (R.cellDarts_eq source)

theorem mergedGeometry_targetArc_length :
    (R.mergedGeometry sourceArc targetArc hdecomp hright hleft hrightNorm
      hleftNorm).targetArc.length = targetArc.length :=
  targetArc.mapTo_length R.keep (R.targetDarts_eq target)

theorem mergedGeometry_targetArc_start :
    (R.mergedGeometry sourceArc targetArc hdecomp hright hleft hrightNorm
      hleftNorm).targetArc.start.1 = targetArc.start.1 :=
  targetArc.mapTo_start R.keep (R.targetDarts_eq target)

end Merged

end Surgery.InnerDiscRegion

namespace GloballyDistinguishedSectionFamily

variable {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The collapse of a disc region absorbing selected regions.**  Let `S` be a distinguished
section family and `R` a disc region of G-cells of its diagram.  Let `absorbed` be at least two
selected regions, and suppose every other selected region avoids `R`.  Suppose that after the
collapse of `R` the merged face is a contiguity region from a cell to a different cell or to a
section, respecting the sections, with nonempty arcs whose total length is at least the weight of
`absorbed`.  Then there is a contradiction. -/
theorem false_of_disc_collapse_singleton
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : Surgery.InnerDiscRegion S.diagram)
    (absorbed : Finset (RegionCandidate D eps S.diagram)) (hsub : absorbed ⊆ S.family)
    (hcard : 2 ≤ absorbed.card)
    (havoid : ∀ a ∈ S.family, a ∉ absorbed → Disjoint a.1 R.faces)
    (H : ContiguityGeometry D eps R.diagram ({R.merged} : Finset R.diagram.toCombMap.Face))
    (hrespects : RegionCandidate.RespectsSections cuts
      (⟨{R.merged}, H⟩ : RegionCandidate D eps R.diagram))
    (hsource : 0 < H.sourceArc.length) (htarget : 0 < H.targetArc.length)
    (hweight : EstimatingSelection.familyWeight RegionCandidate.weight absorbed ≤
      H.sourceArc.length + H.targetArc.length) : False := by
  classical
  have hrest : ∀ a ∈ S.family \ absorbed, Disjoint a.1 R.faces := fun a ha =>
    havoid a (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp ha).2
  have hpair : EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible
      (S.family \ absorbed) := fun a ha b hb hab =>
    S.pairwise a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1 hab
  have hrespects2 : ∀ a ∈ R.regionFamily (S.family \ absorbed) hrest,
      RegionCandidate.RespectsSections cuts a := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := R.regionFamily_profile (S.family \ absorbed) hrest ha
    exact RegionCandidate.respectsSections_of_sameTargetProfile cuts hab
      (R.regionFamily_noLoop (S.family \ absorbed) hrest
        (fun x hx => (S.respects x (Finset.mem_sdiff.mp hx).1).1) ha)
      (S.respects b (Finset.mem_sdiff.mp hb).1)
  have hnondegenerate2 : ∀ a ∈ R.regionFamily (S.family \ absorbed) hrest,
      0 < a.2.sourceArc.length ∧ 0 < a.2.targetArc.length := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := R.regionFamily_profile (S.family \ absorbed) hrest ha
    obtain ⟨hs, ht⟩ := S.nondegenerate b (Finset.mem_sdiff.mp hb).1
    exact ⟨lt_of_lt_of_eq hs hab.2.2.2.symm, lt_of_lt_of_eq ht hab.2.2.1.symm⟩
  have hsplit : EstimatingSelection.familyWeight RegionCandidate.weight (S.family \ absorbed) +
      EstimatingSelection.familyWeight RegionCandidate.weight absorbed =
        EstimatingSelection.familyWeight RegionCandidate.weight S.family := by
    unfold EstimatingSelection.familyWeight
    exact Finset.sum_sdiff hsub
  have hfamily := R.regionFamily_weight (S.family \ absorbed) hrest
  have hcardsplit := Finset.card_sdiff_add_card_eq_card hsub
  have hcard2 := R.regionFamily_card (S.family \ absorbed) hrest
  have hS : S.toRealizedSectionFamily.weight =
      EstimatingSelection.familyWeight RegionCandidate.weight S.family := rfl
  have hweight2 : S.toRealizedSectionFamily.weight ≤
      (H.sourceArc.length + H.targetArc.length) +
        EstimatingSelection.familyWeight RegionCandidate.weight
          (R.regionFamily (S.family \ absorbed) hrest) := by
    omega
  have hcard3 : (R.regionFamily (S.family \ absorbed) hrest).card + 2 ≤ S.family.card := by
    omega
  exact S.false_of_cons_singleton (S.equiv.trans R.oEquivalent) (R.reduced S.reduced)
    (fun d => S.label_admissible (R.val d)) (R.regionFamily (S.family \ absorbed) hrest)
    (R.regionFamily_pairwise (S.family \ absorbed) hrest hpair) hrespects2 hnondegenerate2 H
    (R.regionFamily_avoid_merged (S.family \ absorbed) hrest) hrespects hsource htarget
    hweight2 hcard3

end GloballyDistinguishedSectionFamily

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerDiscRegion.ofPocketRegion
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerDiscRegion.regionFamily_profile
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerDiscRegion.regionFamily_noLoop
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerDiscRegion.mergedGeometry
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerDiscRegion.mergedGeometry_targetArc_start
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.false_of_disc_collapse_singleton
