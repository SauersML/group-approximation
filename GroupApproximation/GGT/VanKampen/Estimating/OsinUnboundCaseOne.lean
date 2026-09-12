import GroupApproximation.GGT.VanKampen.GFaceQuadrilateralRegion
import GroupApproximation.GGT.VanKampen.SurgeryInnerCollapseMerged
import GroupApproximation.GGT.VanKampen.SurgeryInnerCollapseRegions
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.GGT.VanKampen.Estimating.RegionLegalSelection
import GroupApproximation.Meta.AxiomGuard

/-!
# Case 1 of Osin's Lemma 9.4: a new contiguity region contradicts maximality

In the proof of Osin's Appendix Lemma 9.4 (arXiv:math/0411039v3), Case 1 finds, after
passing to an O-equivalent diagram, a subdiagram of G-cells between a long arc `p` of a
relator cell and a long arc `q` (of a relator cell or of a boundary section), cut off by
two short connector words.  It meets no relator cell and no selected region, so it is a
new contiguity region, and adjoining it enlarges the selected system.  This file proves
that contradiction for an actual section family.

The surgery is assembled from three landed pieces:

* the collapse of the G-cell region into one face (`Surgery.InnerGRegion.diagram`), which
  keeps every selected region, its weight, and its target profile
  (`InnerGRegion.regionFamily`, `regionFamily_profile`), and whose merged face is a legal
  insertion face with no internally paired dart;
* the quadrilateral region across the merged face
  (`GFaceWordInsertion.exists_quadrilateral_region`), which inserts the two connectors
  and returns the region `{Q}` with the arc lengths of `p` and `q`;
* the weight count of adjoining a singleton region
  (`RegionCandidate.familyWeight_lt_cons_singleton`).

The new family respects the sections: the new region's target profile is that of `q`,
and every retained region has the profile of the region it came from
(`RegionCandidate.respectsSections_of_sameTargetProfile`).  Its labels are legal letters
of the symmetrized alphabet, so it competes with the optimum
(`RealizedSectionFamily.false_of_quadrilateral_region`).  The optimum is stated through
its two properties, legality and weight maximality among legal families, which are the
`label_admissible` and `weight_maximal` fields of a distinguished section family.
-/

namespace GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen.Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace Embedded.RegionCandidate

/-- Respecting the sections depends only on the target profile. -/
theorem respectsSections_of_sameTargetProfile {D : RelGenSet G Lambda} {eps : ℕ}
    {Delta Xi : DiscDiagram.{u, w, v} W} {lambda c : ℝ} {word : List (RelLetter G Lambda)}
    (cuts : SectionCuts D lambda c word) {a : RegionCandidate D eps Xi}
    {b : RegionCandidate D eps Delta} (hab : SameTargetProfile a b)
    (hb : RespectsSections cuts b) : RespectsSections cuts a := by
  intro hnone
  obtain ⟨j, -, h1, h2⟩ := hb (hab.1.mp hnone)
  refine ⟨j, hnone, ?_, ?_⟩
  · rw [hab.2.1]
    exact h1
  · rw [hab.2.1, hab.2.2]
    exact h2

end Embedded.RegionCandidate

namespace Surgery.InnerGRegion

variable {Delta : DiscDiagram.{u, w, v} W} (R : InnerGRegion Delta)

/-- Every region of a family carried through the collapse has the target profile of the
region it came from. -/
theorem regionFamily_profile {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Disjoint a.1 R.faces) {a : RegionCandidate D eps R.diagram}
    (ha : a ∈ R.regionFamily family havoid) :
    ∃ b ∈ family, RegionCandidate.SameTargetProfile a b := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  refine ⟨b.val, b.property, And.intro ?_ (And.intro ?_ ?_)⟩
  · exact Option.map_eq_none_iff
  · exact CyclicArc.mapTo_start _ _ _
  · exact CyclicArc.mapTo_length _ _ _

/-- No region of a family carried through the collapse contains the merged face. -/
theorem regionFamily_avoid_merged {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Disjoint a.1 R.faces) :
    ∀ a ∈ R.regionFamily family havoid, R.merged ∉ a.1 := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := R.regionFamily_faces family havoid ha
  rw [hab]
  exact R.merged_not_mem_faceSet (havoid b hb)

end Surgery.InnerGRegion

namespace RealizedSectionFamily

/-- **Lemma 9.4, Case 1.**  Let `S` be a section family with legal labels and maximal
weight among legal section families.  Let `R` be a region of G-cells of its diagram that
meets no selected region.  After the collapse of `R`, suppose that the merged face reads
`X ++ q ++ Y ++ p⁻¹`, where `p` is a nonempty arc of a relator cell and `q` is an arc of a
relator cell or of a boundary section, and that `s_1`, `s_2` are legal words of length and
norm at most `ε` with the values of `X` and `Y`.  Then there is a contradiction. -/
theorem false_of_quadrilateral_region {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (hlegal : S.toRealizedRegionFamily.LabelLegal (symmetricLabelAlphabet D))
    (hmax : ∀ other : RealizedSectionFamily D lambda c eps Delta cuts,
      other.toRealizedRegionFamily.LabelLegal (symmetricLabelAlphabet D) →
        other.weight ≤ S.weight)
    (R : Surgery.InnerGRegion S.diagram) (havoid : ∀ a ∈ S.family, Disjoint a.1 R.faces)
    (source : Fin R.diagram.rCellCount) (target : Option (Fin R.diagram.rCellCount))
    (sourceArc : CyclicArc (cellDarts R.diagram source))
    (targetArc : CyclicArc (targetDarts R.diagram target))
    (X Y : List R.diagram.toCombMap.Dart)
    (htrav : (R.diagram.faceBoundary R.merged).darts =
      X ++ targetBoundaryDarts R.diagram target targetArc ++ Y ++ sourceArc.reverseDarts)
    (hsource : 0 < sourceArc.length)
    (hsection : target = none → ∃ j : Fin cuts.count,
      cuts.cut j.castSucc ≤ targetArc.start.val ∧
        targetArc.start.val + targetArc.length ≤ cuts.cut j.succ)
    (s1 s2 : List (RelLetter G Lambda)) (hne1 : s1 ≠ []) (hne2 : s2 ≠ [])
    (hadm1 : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) s1)
    (hinv1 : ∀ l ∈ s1, (symmetricLabelAlphabet D).IsLetter (HullSC.RelWord.inv l))
    (hadm2 : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) s2)
    (hinv2 : ∀ l ∈ s2, (symmetricLabelAlphabet D).IsLetter (HullSC.RelWord.inv l))
    (hval1 : RelLetter.listVal s1 = RelLetter.listVal (dartWord R.diagram X))
    (hval2 : RelLetter.listVal s2 = RelLetter.listVal (dartWord R.diagram Y))
    (hlen1 : s1.length ≤ eps) (hlen2 : s2.length ≤ eps)
    (hnorm1 : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal s1) ≤ eps)
    (hnorm2 : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal s2) ≤ eps) :
    False := by
  have hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (R.diagram.label d) :=
    fun d => hlegal (R.val d)
  obtain ⟨Xi, ⟨hequiv⟩, hred, hlabelXi, Q, H, hHsource, hHtarget, hHnone, hHstart, hretain⟩ :=
    GFaceWordInsertion.exists_quadrilateral_region D (symmetricLabelAlphabet D) eps R.diagram
      hlabel R.merged R.merged_ne_outer R.merged_not_relatorFace R.merged_noInternalFaceDart
      source target sourceArc targetArc X Y htrav hsource s1 s2 hne1 hne2 hadm1 hinv1 hadm2
      hinv2 hval1 hval2 hlen1 hlen2 hnorm1 hnorm2
  obtain ⟨family2, hpair2, -, hweight2, havoid2, hprofile2⟩ :=
    hretain (R.regionFamily S.family havoid) (R.regionFamily_avoid_merged S.family havoid)
      (R.regionFamily_pairwise S.family havoid S.pairwise)
  have hpositive : 0 < H.sourceArc.length := lt_of_lt_of_eq hsource hHsource.symm
  have hlt := RegionCandidate.familyWeight_lt_cons_singleton H havoid2 hpositive
  have hrespects : ∀ a ∈ Finset.cons (⟨{Q}, H⟩ : RegionCandidate D eps Xi) family2
      (RegionCandidate.singleton_not_mem_of_avoid H havoid2),
      RegionCandidate.RespectsSections cuts a := by
    intro a ha
    rcases Finset.mem_cons.mp ha with rfl | ha2
    · intro hnoneQ
      obtain ⟨j, h1, h2⟩ := hsection (hHnone.mp hnoneQ)
      have h3 : cuts.cut j.castSucc ≤ H.targetArc.start.val := by
        rw [hHstart]
        exact h1
      have h4 : H.targetArc.start.val + H.targetArc.length ≤ cuts.cut j.succ := by
        rw [hHstart, hHtarget]
        exact h2
      exact ⟨j, hnoneQ, h3, h4⟩
    · obtain ⟨b, hb, hab⟩ := hprofile2 a ha2
      obtain ⟨c, hc, hbc⟩ := R.regionFamily_profile S.family havoid hb
      exact RegionCandidate.respectsSections_of_sameTargetProfile cuts (hab.trans hbc)
        (S.respects c hc)
  have hle : EstimatingSelection.familyWeight RegionCandidate.weight
      (Finset.cons (⟨{Q}, H⟩ : RegionCandidate D eps Xi) family2
        (RegionCandidate.singleton_not_mem_of_avoid H havoid2)) ≤
      EstimatingSelection.familyWeight RegionCandidate.weight S.family :=
    hmax
      { diagram := Xi
        equiv := S.equiv.trans (R.oEquivalent.trans hequiv)
        reduced := hred (R.reduced S.reduced)
        family := Finset.cons (⟨{Q}, H⟩ : RegionCandidate D eps Xi) family2
          (RegionCandidate.singleton_not_mem_of_avoid H havoid2)
        pairwise := RegionCandidate.cons_singleton_pairwise H havoid2 hpair2
        respects := hrespects }
      hlabelXi
  have heq := hweight2.trans (R.regionFamily_weight S.family havoid)
  omega

end RealizedSectionFamily
end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.respectsSections_of_sameTargetProfile
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.regionFamily_profile
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.regionFamily_avoid_merged
#audit_axioms GroupApproximation.GGT.VanKampen.RealizedSectionFamily.false_of_quadrilateral_region
