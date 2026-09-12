import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundMerged
import GroupApproximation.GGT.VanKampen.SurgeryPinchSplitExtremal
import GroupApproximation.Meta.AxiomGuard

/-!
# Distinguished section families with the unselected G-faces reduced

For Case 2 of Osin's Lemma 9.4 (arXiv:math/0411039v3, §9), lane `hull-unbound` argues on a
globally distinguished section family in which no two distinct G-faces that no selected region
contains meet along an edge or at a vertex.  This file produces such a family with the same number
of regions and the same unbound darts.

* `PinchSplit.transportDistinguished_sum_unboundDarts_card`,
  `PinchSplit.transportDistinguished_faceCount_add_one`: a vertex splitting keeps the unbound darts
  and removes one face.
* `GloballyDistinguishedSectionFamily.UnselectedPinchesSplit`: two corners at one vertex whose
  faces are G-faces that no selected region contains lie on one face.
* `GloballyDistinguishedSectionFamily.exists_unselectedGFacesReduced`: merge G-faces across edges
  (`Surgery.GFaceMerge.transportDistinguished`) and split pinches
  (`PinchSplit.transportDistinguished`) until neither applies.  Each surgery removes one face.
-/

namespace GroupApproximation.GGT.VanKampen

open Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

namespace PinchSplit

/-- The total number of unbound darts is unchanged. -/
theorem transportDistinguished_sum_unboundDarts_card
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram)
    (havoid : ∀ b ∈ S.family, I.Avoids b.1) :
    ∑ j : Fin (transportDistinguished S I havoid).diagram.rCellCount,
        (RegionCandidate.unboundDarts (transportDistinguished S I havoid).family j).card =
      ∑ i : Fin S.diagram.rCellCount, (RegionCandidate.unboundDarts S.family i).card :=
  I.sum_unboundDarts_card S.family havoid

/-- One face disappears. -/
theorem transportDistinguished_faceCount_add_one
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram)
    (havoid : ∀ b ∈ S.family, I.Avoids b.1) :
    (transportDistinguished S I havoid).diagram.toCombMap.faceCount + 1 =
      S.diagram.toCombMap.faceCount :=
  I.faceCount_add_one

end PinchSplit

namespace GloballyDistinguishedSectionFamily

/-- Two corners at one vertex whose faces are G-faces (not the exterior, no relator cell) that no
selected region contains lie on the same face. -/
def UnselectedPinchesSplit (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    Prop :=
  ∀ x y : S.diagram.toCombMap.Dart, S.diagram.toCombMap.sigma.SameCycle x y →
    S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x) ≠ S.diagram.outerFace →
    S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha y) ≠ S.diagram.outerFace →
    (∀ C ∈ S.diagram.relatorCells, C.face ≠ S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x) ∧
      C.face ≠ S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha y)) →
    (∀ b ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x) ∉ b.1 ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha y) ∉ b.1) →
    S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x) =
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha y)

/-- `exists_unselectedGFacesReduced`, by strong induction on the face count. -/
theorem exists_unselectedGFacesReduced_of_faceCount (n : ℕ) :
    ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
      S.diagram.toCombMap.faceCount = n →
      ∃ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        T.UnselectedGFacesMerged ∧ T.UnselectedPinchesSplit ∧ T.family.card = S.family.card ∧
          (∑ i : Fin T.diagram.rCellCount, (RegionCandidate.unboundDarts T.family i).card) =
            ∑ i : Fin S.diagram.rCellCount, (RegionCandidate.unboundDarts S.family i).card := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn
    by_cases hM : S.UnselectedGFacesMerged
    · by_cases hP : S.UnselectedPinchesSplit
      · exact ⟨S, hM, hP, rfl, rfl⟩
      · obtain ⟨x, hx⟩ := Classical.not_forall.mp hP
        obtain ⟨y, hy⟩ := Classical.not_forall.mp hx
        obtain ⟨hsame, hy⟩ := Classical.not_forall.mp hy
        obtain ⟨h1, hy⟩ := Classical.not_forall.mp hy
        obtain ⟨h2, hy⟩ := Classical.not_forall.mp hy
        obtain ⟨h3, hy⟩ := Classical.not_forall.mp hy
        obtain ⟨h4, hne⟩ := Classical.not_forall.mp hy
        obtain ⟨cyc⟩ := PinchSplit.exists_cycles hne
        obtain ⟨I, hI⟩ : ∃ I : PinchSplit.Input S.diagram, ∀ b ∈ S.family, I.Avoids b.1 :=
          ⟨⟨x, y, hsame, cyc, h1, h2, fun C hC => (h3 C hC).1, fun C hC => (h3 C hC).2⟩, h4⟩
        obtain ⟨T, hTM, hTP, hcard, hsum⟩ :=
          ih _ (Nat.lt_of_lt_of_eq (Nat.lt_succ_self _)
              (PinchSplit.transportDistinguished_faceCount_add_one S I hI |>.trans hn))
            (PinchSplit.transportDistinguished S I hI) rfl
        exact ⟨T, hTM, hTP, hcard.trans (PinchSplit.transportDistinguished_card S I hI),
          hsum.trans (PinchSplit.transportDistinguished_sum_unboundDarts_card S I hI)⟩
    · obtain ⟨d, hd⟩ := Classical.not_forall.mp hM
      obtain ⟨h1, hd⟩ := Classical.not_forall.mp hd
      obtain ⟨h2, hd⟩ := Classical.not_forall.mp hd
      obtain ⟨h3, hd⟩ := Classical.not_forall.mp hd
      obtain ⟨h4, hne⟩ := Classical.not_forall.mp hd
      obtain ⟨R, hR⟩ : ∃ R : Surgery.GFaceMerge S.diagram,
          ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1 :=
        ⟨⟨d, hne, h1, h2, h3⟩, h4⟩
      obtain ⟨T, hTM, hTP, hcard, hsum⟩ :=
        ih _ (Nat.lt_of_lt_of_eq (Nat.lt_succ_self _)
            (Surgery.GFaceMerge.transportDistinguished_faceCount_add_one S R hR |>.trans hn))
          (Surgery.GFaceMerge.transportDistinguished S R hR) rfl
      exact ⟨T, hTM, hTP, hcard.trans (Surgery.GFaceMerge.transportDistinguished_card S R hR),
        hsum.trans (Surgery.GFaceMerge.transportDistinguished_sum_unboundDarts_card S R hR)⟩

/-- **Reducing the unselected G-faces.**  A globally distinguished section family can be replaced
by one in which every edge and every vertex between two G-faces that no selected region contains
has one face on both sides, with the same number of regions and the same total number of unbound
darts. -/
theorem exists_unselectedGFacesReduced
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    ∃ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
      T.UnselectedGFacesMerged ∧ T.UnselectedPinchesSplit ∧ T.family.card = S.family.card ∧
        (∑ i : Fin T.diagram.rCellCount, (RegionCandidate.unboundDarts T.family i).card) =
          ∑ i : Fin S.diagram.rCellCount, (RegionCandidate.unboundDarts S.family i).card :=
  exists_unselectedGFacesReduced_of_faceCount _ S rfl

end GloballyDistinguishedSectionFamily

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.transportDistinguished_sum_unboundDarts_card
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.transportDistinguished_faceCount_add_one
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.exists_unselectedGFacesReduced
