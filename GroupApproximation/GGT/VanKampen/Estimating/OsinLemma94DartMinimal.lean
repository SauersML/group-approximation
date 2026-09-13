import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundReduced
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PlanarPieces
import GroupApproximation.Meta.AxiomGuard

/-!
# Dart-minimal distinguished families for Lemma 9.4

Osin (arXiv:math/0411039v3, §9), Lemma 9.4, Case 2 ends: "This contradicts our assumption that
`∑ l(t_i)` is minimal."  `OsinLemma94PlanarPieces` measures a family by the number of darts of
its diagram instead (`GloballyDistinguishedSectionFamily.DartMinimal`), over the optimal
families with the same unbound sum.  This file records how the two reductions of
`OsinUnboundReduced` move that measure.

* `Surgery.GFaceMerge.transportDistinguished_dartCount_add_two`,
  `PinchSplit.transportDistinguished_dartCount`: a G-face merge removes two darts and a pinch split
  keeps them.
* `GloballyDistinguishedSectionFamily.DartMinimal.false_of_dartCount_lt`: no family with the same
  unbound sum has fewer darts.
* `GloballyDistinguishedSectionFamily.DartMinimal.unselectedGFacesMerged`: a dart-minimal family is
  merged across every edge between unselected G-faces, since a merge would remove two darts.
* `exists_reduced_dartCount_le`: the reduction `exists_unselectedGFacesReduced` never adds darts.
  So a dart-minimal family can be taken merged and split at pinches
  (`exists_reduced_dartMinimal`).
-/

namespace GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

universe u w v

section Families

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

namespace Surgery.GFaceMerge

/-- Two darts disappear. -/
theorem transportDistinguished_dartCount_add_two
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : GFaceMerge S.diagram) (havoid : ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1) :
    (transportDistinguished S R havoid).diagram.toCombMap.dartCount + 2 =
      S.diagram.toCombMap.dartCount := by
  classical
  exact EdgeDeletion.dartCount_add_two S.diagram.toCombMap R.dart

end Surgery.GFaceMerge

namespace PinchSplit

/-- The darts are unchanged. -/
theorem transportDistinguished_dartCount
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram)
    (havoid : ∀ b ∈ S.family, I.Avoids b.1) :
    (transportDistinguished S I havoid).diagram.toCombMap.dartCount =
      S.diagram.toCombMap.dartCount :=
  rfl

end PinchSplit

namespace GloballyDistinguishedSectionFamily

/-- A dart-minimal family has no competitor with the same unbound sum and fewer darts. -/
theorem DartMinimal.false_of_dartCount_lt
    {S T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts} (hS : S.DartMinimal)
    (hsum : T.unboundSum = S.unboundSum)
    (hlt : T.diagram.toCombMap.dartCount < S.diagram.toCombMap.dartCount) : False :=
  absurd (hS T hsum) (not_le.mpr hlt)

/-- **A dart-minimal family is merged.**  Merging two unselected G-faces across an edge keeps the
unbound sum and removes two darts. -/
theorem DartMinimal.unselectedGFacesMerged
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts} (hS : S.DartMinimal) :
    S.UnselectedGFacesMerged := by
  intro d h1 h2 h3 h4
  by_contra hne
  obtain ⟨R, hR⟩ : ∃ R : Surgery.GFaceMerge S.diagram,
      ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1 :=
    ⟨⟨d, hne, h1, h2, h3⟩, h4⟩
  refine hS.false_of_dartCount_lt
    (Surgery.GFaceMerge.transportDistinguished_sum_unboundDarts_card S R hR) ?_
  have hdart := Surgery.GFaceMerge.transportDistinguished_dartCount_add_two S R hR
  omega

/-- `exists_reduced_dartCount_le`, by strong induction on the face count. -/
theorem exists_reduced_dartCount_le_of_faceCount (n : ℕ) :
    ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
      S.diagram.toCombMap.faceCount = n →
      ∃ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        T.UnselectedGFacesMerged ∧ T.UnselectedPinchesSplit ∧ T.family.card = S.family.card ∧
          T.unboundSum = S.unboundSum ∧
            T.diagram.toCombMap.dartCount ≤ S.diagram.toCombMap.dartCount := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn
    by_cases hM : S.UnselectedGFacesMerged
    · by_cases hP : S.UnselectedPinchesSplit
      · exact ⟨S, hM, hP, rfl, rfl, le_rfl⟩
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
        obtain ⟨T, hTM, hTP, hcard, hsum, hdart⟩ :=
          ih _ (Nat.lt_of_lt_of_eq (Nat.lt_succ_self _)
              (PinchSplit.transportDistinguished_faceCount_add_one S I hI |>.trans hn))
            (PinchSplit.transportDistinguished S I hI) rfl
        exact ⟨T, hTM, hTP, hcard.trans (PinchSplit.transportDistinguished_card S I hI),
          hsum.trans (PinchSplit.transportDistinguished_sum_unboundDarts_card S I hI),
          hdart.trans_eq (PinchSplit.transportDistinguished_dartCount S I hI)⟩
    · obtain ⟨d, hd⟩ := Classical.not_forall.mp hM
      obtain ⟨h1, hd⟩ := Classical.not_forall.mp hd
      obtain ⟨h2, hd⟩ := Classical.not_forall.mp hd
      obtain ⟨h3, hd⟩ := Classical.not_forall.mp hd
      obtain ⟨h4, hne⟩ := Classical.not_forall.mp hd
      obtain ⟨R, hR⟩ : ∃ R : Surgery.GFaceMerge S.diagram,
          ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1 :=
        ⟨⟨d, hne, h1, h2, h3⟩, h4⟩
      obtain ⟨T, hTM, hTP, hcard, hsum, hdart⟩ :=
        ih _ (Nat.lt_of_lt_of_eq (Nat.lt_succ_self _)
            (Surgery.GFaceMerge.transportDistinguished_faceCount_add_one S R hR |>.trans hn))
          (Surgery.GFaceMerge.transportDistinguished S R hR) rfl
      exact ⟨T, hTM, hTP, hcard.trans (Surgery.GFaceMerge.transportDistinguished_card S R hR),
        hsum.trans (Surgery.GFaceMerge.transportDistinguished_sum_unboundDarts_card S R hR),
        hdart.trans (Nat.le.intro
          (Surgery.GFaceMerge.transportDistinguished_dartCount_add_two S R hR))⟩

/-- **Reducing never adds darts.**  `exists_unselectedGFacesReduced`, with the dart count of the
result at most that of `S`. -/
theorem exists_reduced_dartCount_le
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    ∃ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
      T.UnselectedGFacesMerged ∧ T.UnselectedPinchesSplit ∧ T.family.card = S.family.card ∧
        T.unboundSum = S.unboundSum ∧
          T.diagram.toCombMap.dartCount ≤ S.diagram.toCombMap.dartCount :=
  exists_reduced_dartCount_le_of_faceCount _ S rfl

/-- **A reduced dart-minimal family.**  Every distinguished family can be replaced by one that is
merged across edges, split at pinches and dart-minimal, with the same number of regions and the
same unbound sum.  Reduce a dart-minimal family (`exists_dartMinimal`): the result has no more
darts and the same unbound sum, so it is dart-minimal too. -/
theorem exists_reduced_dartMinimal
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    ∃ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
      T.UnselectedGFacesMerged ∧ T.UnselectedPinchesSplit ∧ T.DartMinimal ∧
        T.family.card = S.family.card ∧ T.unboundSum = S.unboundSum := by
  obtain ⟨T₀, hcard₀, hsum₀, hmin⟩ := exists_dartMinimal S
  obtain ⟨T, hM, hP, hcard, hsum, hdart⟩ := exists_reduced_dartCount_le T₀
  exact ⟨T, hM, hP, fun U hU => hdart.trans (hmin U (hU.trans hsum)),
    hcard.trans hcard₀, hsum.trans hsum₀⟩

end GloballyDistinguishedSectionFamily

end Families

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.transportDistinguished_dartCount_add_two
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.transportDistinguished_dartCount
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.DartMinimal.false_of_dartCount_lt
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.DartMinimal.unselectedGFacesMerged
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.exists_reduced_dartCount_le
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.exists_reduced_dartMinimal
