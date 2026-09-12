import GroupApproximation.GGT.VanKampen.SurgeryGFaceMergeRegions
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.Meta.AxiomGuard

/-!
# Distinguished section families across G-face merges

For Osin's Lemma 9.4 (arXiv:math/0411039v3, §9), lane `hull-unbound` argues on a globally
distinguished section family with no edge between two distinct G-faces that no selected region
contains.  This file produces such a family with the same number of regions and the same
unbound darts.

* `Surgery.GFaceMerge.transportDistinguished`: a distinguished family across one G-face merge
  (`SurgeryGFaceMergeRegions.transportSection`) whose regions avoid the two merged faces.  The
  class the family is maximal in, the section families over diagrams O-equivalent to `Delta`,
  does not change, so maximal weight and minimal card carry over.
* `GloballyDistinguishedSectionFamily.UnselectedGFacesMerged`: every edge between two G-faces
  that no selected region contains has one face on both sides.
* `GloballyDistinguishedSectionFamily.exists_unselectedGFacesMerged`: merge until no such edge
  is left.  Each merge removes one face (`GFaceMerge.faceCount_add_one`).
-/

namespace GroupApproximation.GGT.VanKampen

open Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

namespace Surgery.GFaceMerge

/-- **A distinguished section family across a G-face merge of its diagram.** -/
noncomputable def transportDistinguished
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : GFaceMerge S.diagram) (havoid : ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1) :
    GloballyDistinguishedSectionFamily D lambda c eps Delta cuts where
  toRealizedSectionFamily := transportSection S.toRealizedSectionFamily R havoid
  label_admissible :=
    transportSection_labelLegal S.toRealizedSectionFamily R havoid _ S.label_admissible
  weight_maximal other hother :=
    (S.weight_maximal other hother).trans_eq
      (transportSection_weight S.toRealizedSectionFamily R havoid).symm
  card_minimal other hother hweight :=
    (transportSection_card S.toRealizedSectionFamily R havoid).trans_le
      (S.card_minimal other hother
        (hweight.trans (transportSection_weight S.toRealizedSectionFamily R havoid)))

theorem transportDistinguished_toRealizedSectionFamily
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : GFaceMerge S.diagram) (havoid : ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1) :
    (transportDistinguished S R havoid).toRealizedSectionFamily =
      transportSection S.toRealizedSectionFamily R havoid :=
  rfl

theorem transportDistinguished_diagram
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : GFaceMerge S.diagram) (havoid : ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1) :
    (transportDistinguished S R havoid).diagram = R.diagram :=
  rfl

theorem transportDistinguished_family
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : GFaceMerge S.diagram) (havoid : ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1) :
    (transportDistinguished S R havoid).family = R.regionFamily S.family havoid :=
  rfl

/-- The weight is unchanged. -/
theorem transportDistinguished_weight
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : GFaceMerge S.diagram) (havoid : ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1) :
    (transportDistinguished S R havoid).toRealizedSectionFamily.weight =
      S.toRealizedSectionFamily.weight :=
  transportSection_weight S.toRealizedSectionFamily R havoid

/-- The number of regions is unchanged. -/
theorem transportDistinguished_card
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : GFaceMerge S.diagram) (havoid : ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1) :
    (transportDistinguished S R havoid).family.card = S.family.card :=
  transportSection_card S.toRealizedSectionFamily R havoid

/-- Every transported region avoids the merged face. -/
theorem transportDistinguished_avoid_merged
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : GFaceMerge S.diagram) (havoid : ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1) :
    ∀ a ∈ (transportDistinguished S R havoid).family, R.merged ∉ a.1 :=
  R.regionFamily_avoid_merged S.family havoid

/-- The total number of unbound darts is unchanged. -/
theorem transportDistinguished_sum_unboundDarts_card
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : GFaceMerge S.diagram) (havoid : ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1) :
    ∑ j : Fin (transportDistinguished S R havoid).diagram.rCellCount,
        (RegionCandidate.unboundDarts (transportDistinguished S R havoid).family j).card =
      ∑ i : Fin S.diagram.rCellCount, (RegionCandidate.unboundDarts S.family i).card :=
  R.sum_unboundDarts_card S.family havoid

/-- One face disappears. -/
theorem transportDistinguished_faceCount_add_one
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : GFaceMerge S.diagram) (havoid : ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1) :
    (transportDistinguished S R havoid).diagram.toCombMap.faceCount + 1 =
      S.diagram.toCombMap.faceCount :=
  R.faceCount_add_one

end Surgery.GFaceMerge

namespace GloballyDistinguishedSectionFamily

/-- Every edge between two G-faces (not the exterior, no relator cell) that no selected region
contains has the same face on both sides. -/
def UnselectedGFacesMerged (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    Prop :=
  ∀ d : S.diagram.toCombMap.Dart,
    S.diagram.toCombMap.faceOf d ≠ S.diagram.outerFace →
    S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ≠ S.diagram.outerFace →
    (∀ C ∈ S.diagram.relatorCells, C.face ≠ S.diagram.toCombMap.faceOf d ∧
      C.face ≠ S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)) →
    (∀ b ∈ S.family, S.diagram.toCombMap.faceOf d ∉ b.1 ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∉ b.1) →
    S.diagram.toCombMap.faceOf d = S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)

/-- `exists_unselectedGFacesMerged`, by strong induction on the face count. -/
theorem exists_unselectedGFacesMerged_of_faceCount (n : ℕ) :
    ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
      S.diagram.toCombMap.faceCount = n →
      ∃ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        T.UnselectedGFacesMerged ∧ T.family.card = S.family.card ∧
          (∑ i : Fin T.diagram.rCellCount, (RegionCandidate.unboundDarts T.family i).card) =
            ∑ i : Fin S.diagram.rCellCount, (RegionCandidate.unboundDarts S.family i).card := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn
    by_cases hS : S.UnselectedGFacesMerged
    · exact ⟨S, hS, rfl, rfl⟩
    · obtain ⟨d, hd⟩ := Classical.not_forall.mp hS
      obtain ⟨h1, hd⟩ := Classical.not_forall.mp hd
      obtain ⟨h2, hd⟩ := Classical.not_forall.mp hd
      obtain ⟨h3, hd⟩ := Classical.not_forall.mp hd
      obtain ⟨h4, hne⟩ := Classical.not_forall.mp hd
      obtain ⟨R, hR⟩ : ∃ R : Surgery.GFaceMerge S.diagram,
          ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1 :=
        ⟨⟨d, hne, h1, h2, h3⟩, h4⟩
      obtain ⟨T, hT, hcard, hsum⟩ :=
        ih _ (Nat.lt_of_lt_of_eq (Nat.lt_succ_self _)
            (Surgery.GFaceMerge.transportDistinguished_faceCount_add_one S R hR |>.trans hn))
          (Surgery.GFaceMerge.transportDistinguished S R hR) rfl
      exact ⟨T, hT, hcard.trans (Surgery.GFaceMerge.transportDistinguished_card S R hR),
        hsum.trans (Surgery.GFaceMerge.transportDistinguished_sum_unboundDarts_card S R hR)⟩

/-- **Merging the unselected G-faces.**  A globally distinguished section family can be
replaced by one in which every edge between two G-faces that no selected region contains has
the same face on both sides, with the same number of regions and the same total number of
unbound darts. -/
theorem exists_unselectedGFacesMerged
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    ∃ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
      T.UnselectedGFacesMerged ∧ T.family.card = S.family.card ∧
        (∑ i : Fin T.diagram.rCellCount, (RegionCandidate.unboundDarts T.family i).card) =
          ∑ i : Fin S.diagram.rCellCount, (RegionCandidate.unboundDarts S.family i).card :=
  exists_unselectedGFacesMerged_of_faceCount _ S rfl

end GloballyDistinguishedSectionFamily

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.transportDistinguished
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.transportDistinguished_weight
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.transportDistinguished_card
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.transportDistinguished_avoid_merged
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.transportDistinguished_sum_unboundDarts_card
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.exists_unselectedGFacesMerged
