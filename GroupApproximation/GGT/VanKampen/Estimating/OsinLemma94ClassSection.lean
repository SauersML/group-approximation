import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassCoversOtherFacing
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellFactorInput
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CuttingClassesClosed
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SectionResiduals
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4 over the classes: the section from the class count

Osin (math/0411039v3, §9), proof of Lemma 9.4.  `osinLemma94Section_of_planarPieces` takes the
side-level count piece `OsinLemma94PolygonCountInput`, whose covering half
`P.Covers L` (factor one) is produced only from `OsinLemma94UnboundSameCellStatement`, false as
spelled.  The unbound stretches with their own cell across are paid by a factor on the class words
instead (`OsinLemma94ClassPolygons.ClassCovers M L`).  This module passes from the class count to
Lemma 9.4.

* `OsinLemma94ClassCasesInput` (residual): Case 1 and Case 2 of Lemma 9.4 on class words, the
  `hcases` of `OsinLemma94ClassPolygons.unbound_lt_of_classes`.
* `osinLemma94Section_of_classCount`: Lemma 9.4 from the class count and the class-word cases,
  with the closed metric half `osinLemma94AntiparallelMetric` and the closed realization
  `osinLemma94PolygonRealizationInput`.
* `OsinLemma94ClassPolygons.card_cuttingClasses_add_otherClasses`,
  `classCount_le_six_mul_otherClasses`, `classBudget_of_otherClasses`: (38) for classes.  The
  cutting classes number at most `4 m + 1` (`card_cuttingClasses_le_of_dartMinimal`, closed), and
  a budget polygon has a class of kind `cell`, so `k_i ≤ 6 m_i` and a budget `K n` on the other
  classes gives the class budget `6 K n`.
* `OsinLemma94ClassEndLoopsInput` (residual): at the parameters of Lemma 9.4, class polygons with
  the other classes budgeted, the (A1) sides across unbound other-facing darts, and end loops of
  bounded length, as in `OsinLemma94OtherFacingCover.otherFacingCover_of_endLoops`.
* `osinLemma94ClassCountInput_of_endLoops`: the class count from the end loops and hypothesis (ii)
  `OsinLemma94SameCellFactorInput`, through
  `OsinLemma94OtherFacingCover.classCovers_of_endLoops_sameCellFactor`, with `M = ⌈1/λ⌉₊ + 1`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 9.4 inside the proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- **Case 1 and Case 2 of Lemma 9.4, on class words (residual).**  At the parameters of
Lemma 9.4, for `ρ` large, with clause (b) of Lemma 9.7 below the number of relator cells of `Δ` in
scope: for a dart-minimal distinguished system, maximal polygons and any class polygons, no
connector pair on the class words is backwards.  This is the `hcases` of
`OsinLemma94ClassPolygons.unbound_lt_of_classes`. -/
def OsinLemma94ClassCasesInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    ∀ (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
                      (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k)
                        (Q.classCount k) (Q.relatorClasses k) (Q.longClasses k) eps),
                      C.b' < C.b → False

/-- **Osin's Lemma 9.4 from the class count and the class-word cases.**  The thresholds are the
maxima of the pieces', with `ρ₀ ≥ 4 L²` and `ρ₀ ≥ 4 M² ρ_metric`.  The given family is replaced
by a dart-minimal one with the same number of regions and the same unbound sum. -/
theorem osinLemma94Section_of_classCount
    (hcount : OsinLemma94ClassCountInput.{u, w, v})
    (hcases : OsinLemma94ClassCasesInput.{u, w, v}) :
    OsinLemma94SectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps1, hcountE⟩ := hcount D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  have hhyperE : ∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic (symmetricLabelAlphabet D).alphabet.carrier delta := by
    rw [symmetricLabelAlphabet.carrier_eq]
    exact hhyper
  obtain ⟨eps2, hmetricE⟩ :=
    osinLemma94AntiparallelMetric (symmetricLabelAlphabet D) hhyperE lambda (c + 2) hlambda
      (by linarith)
  obtain ⟨eps3, hrealEps⟩ :=
    osinLemma94PolygonRealizationInput D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps4, hcasesEps⟩ := hcases D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max eps1 (max eps2 (max eps3 eps4)), fun eps heps => ?_⟩
  simp only [max_le_iff] at heps
  obtain ⟨he1, he2, he3, he4⟩ := heps
  obtain ⟨K, M, L, hM, rho1, hrho1, hcountEps⟩ := hcountE eps he1
  obtain ⟨rho2, _, hmetricEps⟩ := hmetricE eps he2 K
  obtain ⟨rho3, _, hrealRho⟩ := hrealEps eps he3
  obtain ⟨rho4, _, hcasesRho⟩ := hcasesEps eps he4
  refine ⟨max rho1 (max (4 * M * M * rho2) (max (4 * L * L) (max rho3 rho4))),
    lt_of_lt_of_le hrho1 (le_max_left _ _), fun rho hrho => ?_⟩
  simp only [max_le_iff] at hrho
  obtain ⟨hr1, hr2, hrL, hr3, hr4⟩ := hrho
  intro W hW Delta cuts hleast hcells hbelow S hcard
  obtain ⟨T, hTcard, hTsum, hTmin⟩ := S.exists_dartMinimal
  have hTcard' : T.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) := by
    rw [hTcard]
    exact hcard
  obtain ⟨P, hP⟩ := hrealRho rho hr3 W hW Delta cuts hleast hcells T hTcard' hTmin
  obtain ⟨Q, hbudget, hcovers⟩ :=
    hcountEps rho hr1 W hW Delta cuts hleast hcells hbelow T hTcard' hTmin P hP
  rw [← GloballyDistinguishedSectionFamily.unboundSum_cast S, ← hTsum,
    GloballyDistinguishedSectionFamily.unboundSum_cast T]
  exact Q.unbound_lt_of_classes hcells hbudget hcovers hM hr2 hrL hmetricEps
    (fun k C hback =>
      hcasesRho rho hr4 W hW Delta cuts hleast hcells hbelow T hTcard' hTmin P hP Q k C hback)

namespace OsinLemma94ClassPolygons

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- Every class is a cutting class or another class. -/
theorem card_cuttingClasses_add_otherClasses (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) :
    (Q.cuttingClasses k).card + (Q.otherClasses k).card = Q.classCount k := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range (Q.classCount k))
    (fun i => Q.classKind k i = .cutting)
  rw [Finset.card_range] at h
  unfold cuttingClasses otherClasses
  convert h

/-- **(38) for classes, at a budget polygon**: `k_i ≤ 6 m_i`, where `m_i` counts the other
classes. -/
theorem classCount_le_six_mul_otherClasses (hS : S.DartMinimal) (hmax : P.Maximal)
    (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} (hk : k ∈ Q.budgetPolygons) :
    Q.classCount k ≤ 6 * (Q.otherClasses k).card := by
  have hcut := Q.card_cuttingClasses_le_of_dartMinimal hS hmax k
  have hsum := Q.card_cuttingClasses_add_otherClasses k
  have hpos : 0 < (Q.otherClasses k).card := by
    classical
    simp only [budgetPolygons, Finset.mem_filter] at hk
    obtain ⟨-, -, i, hi, j, hj⟩ := hk
    refine Finset.card_pos.2 ⟨i, (Q.mem_otherClasses k i).2 ⟨hi, ?_⟩⟩
    rw [hj]
    exact fun h => by cases h
  omega

/-- **The class budget from the other classes.** -/
theorem classBudget_of_otherClasses (hS : S.DartMinimal) (hmax : P.Maximal)
    (Q : OsinLemma94ClassPolygons P) {K : ℕ}
    (h : ∑ k ∈ Q.budgetPolygons, (Q.otherClasses k).card ≤ K * Delta.rCellCount) :
    Q.ClassBudget (6 * K) := by
  unfold ClassBudget
  calc ∑ k ∈ Q.budgetPolygons, Q.classCount k
      ≤ ∑ k ∈ Q.budgetPolygons, 6 * (Q.otherClasses k).card :=
        Finset.sum_le_sum fun k hk => Q.classCount_le_six_mul_otherClasses hS hmax hk
    _ = 6 * ∑ k ∈ Q.budgetPolygons, (Q.otherClasses k).card := (Finset.mul_sum _ _ _).symm
    _ ≤ 6 * (K * Delta.rCellCount) := by gcongr
    _ = 6 * K * Delta.rCellCount := by ring

end OsinLemma94ClassPolygons

/-- **The end loops of the class cover (residual).**  At the parameters of Lemma 9.4, with `K`
and `B` chosen after `ε`, for `ρ` large, with clause (b) of Lemma 9.7 below the number of relator
cells in scope: for a dart-minimal distinguished system and maximal polygons there are class
polygons whose classes of kind other than `cutting` number at most `K n` over the budget polygons,
such that an unbound dart facing no selected region and not its own cell lies across an (A1) side,
with end loops of at most `B` darts carrying the reverses of the darts on single-class polygons
that lie in no (A1) class of a budget polygon.  These are the hypotheses of
`OsinLemma94OtherFacingCover.otherFacingCover_of_endLoops` other than `hvalue`, `hcells`, `hcard`,
with the class budget replaced by the other-class budget. -/
def OsinLemma94ClassEndLoopsInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ K B : ℕ, ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    ∃ Q : OsinLemma94ClassPolygons P,
                      (∑ k ∈ Q.budgetPolygons, (Q.otherClasses k).card ≤
                        K * Delta.rCellCount) ∧
                      (∀ (i : Fin S.diagram.rCellCount) (d : S.diagram.toCombMap.Dart),
                        d ∈ S.unboundOffRegions i →
                          (cell S.diagram i).face ≠
                              S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) →
                            ∃ k s, s < P.sideCount k ∧ s ∈ P.relatorSides k ∧
                              S.diagram.toCombMap.alpha d ∈ P.sideDarts k s) ∧
                      ∃ (classEnd : Fin P.count → ℕ → Bool → List S.diagram.toCombMap.Dart)
                        (regionEnd : RegionCandidate D eps S.diagram → Fin 4 →
                          List S.diagram.toCombMap.Dart),
                        (∀ k ∈ Q.budgetPolygons, ∀ i < Q.classCount k, ∀ b,
                          (classEnd k i b).length ≤ B) ∧
                        (∀ a ∈ S.family, ∀ t, (regionEnd a t).length ≤ B) ∧
                        ∀ (i : Fin S.diagram.rCellCount) (d : S.diagram.toCombMap.Dart),
                          d ∈ S.unboundOffRegions i →
                            (cell S.diagram i).face ≠
                                S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) →
                              ∀ k s, Q.classCount k = 1 → s < P.sideCount k →
                                s ∈ P.relatorSides k →
                                S.diagram.toCombMap.alpha d ∈ P.sideDarts k s →
                                  (∃ k' i', i' < Q.classCount k' ∧ i' ∈ Q.relatorClasses k' ∧
                                      S.diagram.toCombMap.alpha d ∈ Q.classDarts k' i') ∨
                                    (∃ k' ∈ Q.budgetPolygons, ∃ i' < Q.classCount k', ∃ b,
                                      S.diagram.toCombMap.alpha d ∈ classEnd k' i' b) ∨
                                    ∃ a ∈ S.family, ∃ t,
                                      S.diagram.toCombMap.alpha d ∈ regionEnd a t

/-- **The class count from the end loops and the same-cell factor.**  The class budget is
`6 K n` (`classBudget_of_otherClasses`), and the cover has factor `⌈1/λ⌉₊ + 1` and slack
`(⌈1/λ⌉₊ + 1) (24 ε + 2 (6 K + 24) B) + 25 ⌈c/λ⌉₊`. -/
theorem osinLemma94ClassCountInput_of_endLoops
    (hloops : OsinLemma94ClassEndLoopsInput.{u, w, v})
    (hfactor : OsinLemma94SameCellFactorInput.{u, w, v}) :
    OsinLemma94ClassCountInput.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, hL⟩ := hloops D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨K, B, rho1, hrho1, hK⟩ := hL eps heps
  obtain ⟨rho2, _, hF⟩ := hfactor D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16 eps
  refine ⟨6 * K, ⌈1 / lambda⌉₊ + 1,
    (⌈1 / lambda⌉₊ + 1) * (24 * eps + 2 * (6 * K + 24) * B) + 25 * ⌈c / lambda⌉₊,
    Nat.succ_pos _, max rho1 (max rho2 (⌈c / lambda⌉₊ + 2)),
    lt_of_lt_of_le hrho1 (le_max_left _ _), fun rho hrho => ?_⟩
  simp only [max_le_iff] at hrho
  obtain ⟨hr1, hr2, hrc⟩ := hrho
  intro W hW Delta cuts hleast hcells hbelow S hcard hmin P hmax
  obtain ⟨Q, hother, hside, classEnd, regionEnd, hclassEnd, hregionEnd, hbubble⟩ :=
    hK rho hr1 W hW Delta cuts hleast hcells hbelow S hcard hmin P hmax
  have hrhoc : c < lambda * rho := by
    have hceil : c / lambda ≤ ⌈c / lambda⌉₊ := Nat.le_ceil _
    have hcast : ((⌈c / lambda⌉₊ : ℕ) : ℝ) + 1 ≤ rho := by
      exact_mod_cast (by omega : ⌈c / lambda⌉₊ + 1 ≤ rho)
    have hlt : c < rho * lambda := (div_lt_iff₀ hlambda).mp (by linarith)
    linarith [mul_comm lambda (rho : ℝ)]
  have hbudget := Q.classBudget_of_otherClasses hmin hmax hother
  exact ⟨Q, hbudget, OsinLemma94OtherFacingCover.classCovers_of_endLoops_sameCellFactor Q
    (S.cell_listVal_ne_one hW hlambda hrhoc) hcells hcard hbudget hside classEnd regionEnd
    hclassEnd hregionEnd hbubble (hF rho hr2 W hW Delta cuts hleast hcells hbelow S hcard hmin)⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94Section_of_classCount
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.classBudget_of_otherClasses
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94ClassCountInput_of_endLoops
