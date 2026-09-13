import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundReduced
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94AntiparallelMetric
import GroupApproximation.Meta.AxiomGuard

/-!
# Dart-minimal distinguished families for Lemma 9.4

Osin (arXiv:math/0411039v3, §9), Lemma 9.4, Case 2 ends: "This contradicts our assumption that
`∑ l(t_i)` is minimal."  Osin minimizes the total length of the cutting paths.  A
`GloballyDistinguishedSectionFamily` carries no cutting paths and has no field for that
minimality.  The measure used here instead is the number of darts of the diagram, over the
distinguished families with the same number of regions and the same `S` (the number of unbound
darts of the relator cells).  Case 2 replaces a stretch of boundary by a shorter connector, which
removes darts.

* `GloballyDistinguishedSectionFamily.unboundSum`: Osin's `S`.
* `GloballyDistinguishedSectionFamily.DartMinimal`: no distinguished family with the same card and
  the same `S` lies on a diagram with fewer darts.  `exists_dartMinimal`: one exists, by strong
  induction on the dart count.
* `Surgery.GFaceMerge.transportDistinguished_dartCount_add_two`,
  `PinchSplit.transportDistinguished_dartCount`: a G-face merge removes two darts and a pinch split
  keeps them.  So the reduction `exists_unselectedGFacesReduced` never adds darts
  (`exists_reduced_dartCount_le`), and a dart-minimal family can be taken reduced
  (`exists_reduced_dartMinimal`).
* `OsinLemma94PlanarPolygons.ofUnboundSumEq`: component polygons read the family only through `S`.
* `OsinLemma94PlanarRunInputReduced`, `osinLemma94PlanarRunInput_of_reduced`: the planar half of
  Lemma 9.4 may assume the family merged, split at pinches and dart-minimal.
  `osinLemma94Section_of_planarRunInputReduced`: with the closed metric half, this Prop alone gives
  `OsinLemma94SectionStatement`.
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

/-- Osin's `S`: the total number of unbound darts of the relator cells. -/
noncomputable def unboundSum (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    ℕ :=
  ∑ i : Fin S.diagram.rCellCount, (RegionCandidate.unboundDarts S.family i).card

/-- **Dart-minimal.**  No distinguished family with the same number of regions and the same `S`
lies on a diagram with fewer darts. -/
def DartMinimal (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) : Prop :=
  ∀ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
    T.family.card = S.family.card → T.unboundSum = S.unboundSum →
      S.diagram.toCombMap.dartCount ≤ T.diagram.toCombMap.dartCount

/-- `exists_dartMinimal`, by strong induction on the dart count. -/
theorem exists_dartMinimal_of_dartCount (n : ℕ) :
    ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
      S.diagram.toCombMap.dartCount = n →
      ∃ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        T.DartMinimal ∧ T.family.card = S.family.card ∧ T.unboundSum = S.unboundSum := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn
    by_cases hS : S.DartMinimal
    · exact ⟨S, hS, rfl, rfl⟩
    · obtain ⟨U, hU⟩ := Classical.not_forall.mp hS
      obtain ⟨hcard, hU⟩ := Classical.not_forall.mp hU
      obtain ⟨hsum, hlt⟩ := Classical.not_forall.mp hU
      obtain ⟨T, hT, hTcard, hTsum⟩ := ih _ ((not_le.mp hlt).trans_eq hn) U rfl
      exact ⟨T, hT, hTcard.trans hcard, hTsum.trans hsum⟩

/-- **A dart-minimal family exists** with the same number of regions and the same `S`. -/
theorem exists_dartMinimal (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    ∃ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
      T.DartMinimal ∧ T.family.card = S.family.card ∧ T.unboundSum = S.unboundSum :=
  exists_dartMinimal_of_dartCount _ S rfl

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
same `S`. -/
theorem exists_reduced_dartMinimal
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    ∃ T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
      T.UnselectedGFacesMerged ∧ T.UnselectedPinchesSplit ∧ T.DartMinimal ∧
        T.family.card = S.family.card ∧ T.unboundSum = S.unboundSum := by
  obtain ⟨T₀, hmin, hcard₀, hsum₀⟩ := exists_dartMinimal S
  obtain ⟨T, hM, hP, hcard, hsum, hdart⟩ := exists_reduced_dartCount_le T₀
  exact ⟨T, hM, hP, fun U hU hUsum => hdart.trans (hmin U (hU.trans hcard) (hUsum.trans hsum)),
    hcard.trans hcard₀, hsum.trans hsum₀⟩

end GloballyDistinguishedSectionFamily

namespace OsinLemma94PlanarPolygons

/-- **Component polygons read the family only through `S`.** -/
def ofUnboundSumEq {K : ℕ} {S T : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    (P : OsinLemma94PlanarPolygons D lambda c eps K T) (h : T.unboundSum = S.unboundSum) :
    OsinLemma94PlanarPolygons D lambda c eps K S where
  count := P.count
  sideCount := P.sideCount
  corner := P.corner
  word := P.word
  relatorSides := P.relatorSides
  longSides := P.longSides
  side_budget := P.side_budget
  closed := P.closed
  step := P.step
  quasiGeodesic := P.quasiGeodesic
  short := P.short
  covers := by
    have hS : (∑ i : Fin S.diagram.rCellCount,
        ((RegionCandidate.unboundDarts S.family i).card : ℝ)) = (S.unboundSum : ℝ) := by
      rw [GloballyDistinguishedSectionFamily.unboundSum, Nat.cast_sum]
    have hT : (∑ i : Fin T.diagram.rCellCount,
        ((RegionCandidate.unboundDarts T.family i).card : ℝ)) = (T.unboundSum : ℝ) := by
      rw [GloballyDistinguishedSectionFamily.unboundSum, Nat.cast_sum]
    rw [hS, ← h, ← hT]
    exact P.covers
  no_antiparallel := P.no_antiparallel

end OsinLemma94PlanarPolygons

end Families

/-- **The diagram half of Lemma 9.4 over reduced dart-minimal families.**  This is
`OsinLemma94PlanarRunInput` with three more hypotheses on `S`:
* merged across edges (`UnselectedGFacesMerged`);
* split at pinches (`UnselectedPinchesSplit`);
* dart-minimal (`DartMinimal`), which stands in for Case 2's "`∑ l(t_i)` is minimal". -/
def OsinLemma94PlanarRunInputReduced : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ K : ℕ, ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) →
                S.UnselectedGFacesMerged → S.UnselectedPinchesSplit → S.DartMinimal →
                  Nonempty (OsinLemma94PlanarPolygons D lambda c eps K S)

/-- **The planar half of Lemma 9.4 may assume the family reduced and dart-minimal.**  Replace `S`
by `exists_reduced_dartMinimal`: its card is the same, so the Euler bound still holds, and its `S`
is the same, so its polygons are polygons for `S` (`ofUnboundSumEq`). -/
theorem osinLemma94PlanarRunInput_of_reduced
    (hrun : OsinLemma94PlanarRunInputReduced.{u, w, v}) :
    OsinLemma94PlanarRunInput.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨K, eps0, hK⟩ := hrun D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨K, eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := hK eps heps
  refine ⟨rho0, hrho0, fun rho hr W hW Delta cuts hleast hcells S hcard => ?_⟩
  obtain ⟨T, hM, hP, hmin, hTcard, hTsum⟩ :=
    GloballyDistinguishedSectionFamily.exists_reduced_dartMinimal S
  obtain ⟨P⟩ := hrho rho hr W hW Delta cuts hleast hcells T (hTcard.trans_le hcard) hM hP hmin
  exact ⟨P.ofUnboundSumEq hTsum⟩

/-- **Lemma 9.4 from the planar half over reduced dart-minimal families**, with the closed
oriented metric half `osinLemma94AntiparallelMetric`. -/
theorem osinLemma94Section_of_planarRunInputReduced
    (hrun : OsinLemma94PlanarRunInputReduced.{u, w, v}) :
    OsinLemma94SectionStatement.{u, w, v} :=
  osinLemma94Section_of_pieces osinLemma94AntiparallelMetric
    (osinLemma94PlanarRunInput_of_reduced hrun)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.transportDistinguished_dartCount_add_two
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.transportDistinguished_dartCount
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.exists_dartMinimal
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.exists_reduced_dartMinimal
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94PlanarPolygons.ofUnboundSumEq
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94PlanarRunInput_of_reduced
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94Section_of_planarRunInputReduced
