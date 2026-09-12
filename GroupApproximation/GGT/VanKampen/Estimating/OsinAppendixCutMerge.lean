import GroupApproximation.GGT.VanKampen.SurgeryInnerCollapseRegions
import GroupApproximation.GGT.VanKampen.Estimating.SingletonFaceRegion
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOne
import GroupApproximation.GGT.VanKampen.Estimating.RegionLegalSelection
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.7(b): merging selected regions across a pocket

In the proof of Osin's Appendix Lemma 9.7(b) (arXiv:math/0411039v3), two distinct regions of
the distinguished system `M` from one cell `Π` to one section `q_j` bound a pocket `Γ_1`
with `∂Γ_1 = s_1 t_1 s_2 t_2`.  If `Γ_1` contains no R-cell, the two regions and the pocket
form one contiguity region from `Π` to `q_j`, whose arcs contain both pairs of arcs.
Replacing the selected regions it contains by this one region keeps the total weight and
lowers the number of regions, against the choice of `M`.

## What is proved here

* `GloballyDistinguishedSectionFamily.false_of_weight_le_of_card_lt`: a legal section family
  at least as heavy as the distinguished one, with fewer regions, is a contradiction;
* `GloballyDistinguishedSectionFamily.false_of_cons_singleton`: the same for a family on an
  O-equivalent diagram obtained by adjoining one singleton region to a family with at least two
  regions fewer, whose total weight is at least the distinguished weight;
* `GloballyDistinguishedSectionFamily.false_of_collapse_singleton`: the collapse of a region of
  G-cells into one face absorbing at least two selected regions, where the merged face is a
  contiguity region respecting the sections whose arcs are at least as long as the absorbed
  regions' arcs together, is a contradiction.  The retained regions are carried through the
  collapse with their weight and target profile.
-/

namespace GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen.Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace GloballyDistinguishedSectionFamily

variable {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- A legal section family at least as heavy as the distinguished family and with fewer
regions contradicts the choice of the distinguished family: maximal weight, then minimal
number of regions. -/
theorem false_of_weight_le_of_card_lt
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (other : RealizedSectionFamily D lambda c eps Delta cuts)
    (hlegal : other.toRealizedRegionFamily.LabelLegal (symmetricLabelAlphabet D))
    (hweight : S.toRealizedSectionFamily.weight ≤ other.weight)
    (hcard : other.family.card < S.family.card) : False := by
  have hle := S.weight_maximal other hlegal
  have hmin := S.card_minimal other hlegal (le_antisymm hle hweight)
  omega

/-- **Adjoining one region in place of two or more.**  Let `Xi` be a reduced diagram
O-equivalent to `Delta` with legal labels, carrying a section family `family`.  Adjoin a
singleton region at a face `f` avoided by `family`, with nonempty arcs and respecting the
sections.  If the new family is at least as heavy as the distinguished family `S` and `family`
has at least two regions fewer than `S`, there is a contradiction. -/
theorem false_of_cons_singleton
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {Xi : DiscDiagram.{u, w, v} W} (hequiv : OEquivalentDiscDiagram Delta Xi)
    (hred : Xi.Reduced)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (Xi.label d))
    (family : Finset (RegionCandidate D eps Xi))
    (hpairwise : EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family)
    (hrespects : ∀ a ∈ family, RegionCandidate.RespectsSections cuts a)
    (hnondegenerate : ∀ a ∈ family, 0 < a.2.sourceArc.length ∧ 0 < a.2.targetArc.length)
    {f : Xi.toCombMap.Face} (H : ContiguityGeometry D eps Xi ({f} : Finset Xi.toCombMap.Face))
    (havoid : ∀ a ∈ family, f ∉ a.1)
    (hrespectsH : RegionCandidate.RespectsSections cuts
      (⟨{f}, H⟩ : RegionCandidate D eps Xi))
    (hsource : 0 < H.sourceArc.length) (htarget : 0 < H.targetArc.length)
    (hweight : S.toRealizedSectionFamily.weight ≤
      (H.sourceArc.length + H.targetArc.length) +
        EstimatingSelection.familyWeight RegionCandidate.weight family)
    (hcard : family.card + 2 ≤ S.family.card) : False := by
  have hrespects2 : ∀ a ∈ Finset.cons (⟨{f}, H⟩ : RegionCandidate D eps Xi) family
      (RegionCandidate.singleton_not_mem_of_avoid H havoid),
      RegionCandidate.RespectsSections cuts a := by
    intro a ha
    rcases Finset.mem_cons.mp ha with rfl | ha2
    · exact hrespectsH
    · exact hrespects a ha2
  have hnondegenerate2 : ∀ a ∈ Finset.cons (⟨{f}, H⟩ : RegionCandidate D eps Xi) family
      (RegionCandidate.singleton_not_mem_of_avoid H havoid),
      0 < a.2.sourceArc.length ∧ 0 < a.2.targetArc.length := by
    intro a ha
    rcases Finset.mem_cons.mp ha with rfl | ha2
    · exact ⟨hsource, htarget⟩
    · exact hnondegenerate a ha2
  have hcons := RegionCandidate.familyWeight_cons_singleton H havoid
  have hconscard := Finset.card_cons (RegionCandidate.singleton_not_mem_of_avoid H havoid)
  have hle : S.toRealizedSectionFamily.weight ≤
      EstimatingSelection.familyWeight RegionCandidate.weight
        (Finset.cons (⟨{f}, H⟩ : RegionCandidate D eps Xi) family
          (RegionCandidate.singleton_not_mem_of_avoid H havoid)) := by
    omega
  have hlt : (Finset.cons (⟨{f}, H⟩ : RegionCandidate D eps Xi) family
      (RegionCandidate.singleton_not_mem_of_avoid H havoid)).card < S.family.card := by
    omega
  exact S.false_of_weight_le_of_card_lt
    { diagram := Xi
      equiv := hequiv
      reduced := hred
      family := Finset.cons (⟨{f}, H⟩ : RegionCandidate D eps Xi) family
        (RegionCandidate.singleton_not_mem_of_avoid H havoid)
      pairwise := RegionCandidate.cons_singleton_pairwise H havoid hpairwise
      respects := hrespects2
      nondegenerate := hnondegenerate2 }
    hlabel hle hlt

/-- **The collapse of a region absorbing selected regions.**  Let `S` be a distinguished section
family and `R` a region of G-cells of its diagram.  Let `absorbed` be at least two selected
regions, and suppose every other selected region avoids `R`.  Suppose that after the collapse
of `R` the merged face is a contiguity region respecting the sections, with nonempty arcs whose
total length is at least the weight of `absorbed`.  Then there is a contradiction. -/
theorem false_of_collapse_singleton
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : Surgery.InnerGRegion S.diagram)
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

#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.false_of_weight_le_of_card_lt
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.false_of_cons_singleton
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.false_of_collapse_singleton
