import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94AntiparallelMetricTwoThreshold
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BudgetFilter
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4 over the classes, at two thresholds

Osin (math/0411039v3, §9), proof of Lemma 9.4.  `osinLemma94Section_of_classCount` refutes the backwards
class-word pairs at one threshold `ε` (`OsinLemma94ClassCasesInput`).  A pair with an endpoint strictly
inside a gap of a class word does not reduce to one with endpoints on sides at the same `ε`: moving an
endpoint to a corner lengthens a connector and shortens a segment by up to half a gap.  The gaps have at
most `B = ⌈(c + 2) / λ⌉₊` letters (`OsinLemma94ClassPolygons.gap_length_le`).  So this module takes the
pairs from the metric half at two thresholds (`osinLemma94AntiparallelMetricTwo`): connectors below
`ε − B`, segments above `ε + B`.

* `OsinLemma94DensePolygonsAntiparallelTwo.exists_of_budget_on`: the budget filter at two thresholds.
* `OsinLemma94ClassPolygons.unbound_lt_of_classesTwo`: the contradiction at fixed parameters.
* `OsinLemma94ClassCasesTwoThresholdInput` (residual): no backwards class-word pair has connectors
  below `ε − B` and segments above `ε + B`.
* `osinLemma94Section_of_classCountTwoThreshold`: Lemma 9.4 from the class count and these cases.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 9.4 inside the proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- **The budget filter at two thresholds**: as `OsinLemma94DensePolygonsAntiparallel.exists_of_budget_on`,
over the polygons of `s` that carry the `A`-sides. -/
theorem OsinLemma94DensePolygonsAntiparallelTwo.exists_of_budget_on {G : Type u} [Group G]
    {Lambda : Type w} {D : RelGenSet G Lambda} {lambda c : ℝ} {epsC epsL rho K : ℕ}
    (hmetric : OsinLemma94DensePolygonsAntiparallelTwo D lambda c epsC epsL rho K)
    {n d : ℕ} (hn : 0 < n) (sideCount : Fin d → ℕ) (v : Fin d → ℕ → G)
    (word : Fin d → ℕ → List (RelLetter G Lambda)) (A B : Fin d → Set ℕ) (s : Finset (Fin d))
    (hs : ∀ k, ∀ i < sideCount k, i ∈ A k → k ∈ s)
    (hbudget : (∑ k ∈ s, sideCount k) ≤ K * n)
    (hclosed : ∀ k, v k (sideCount k) = v k 0)
    (hstep : ∀ k i, i < sideCount k → v k (i + 1) = v k i * RelLetter.listVal (word k i))
    (hqg : ∀ k i, i < sideCount k → i ∈ A k ∨ i ∈ B k →
      IsLambdaCQuasiGeodesicWord D lambda c (word k i))
    (hshort : ∀ k i, i < sideCount k → i ∉ B k →
      HullSC.RelWord.IsAdmissible D (word k i) ∧ (word k i).length ≤ epsL)
    (hdense : (n : ℝ) * Real.sqrt (rho : ℝ) ≤
      ∑ k : Fin d, classWordLength (word k) (sideCount k) (A k)) :
    ∃ k : Fin d, ∃ C : WordConnectorPair D (v k) (word k) (sideCount k) (A k) (B k) epsC,
      C.b' < C.b ∧
        epsL < WordMetric.wordDist D.alphabet.carrier
          (OsinComponents.vertex (v k C.source) (word k C.source) C.a)
          (OsinComponents.vertex (v k C.source) (word k C.source) C.a') ∧
        epsL < WordMetric.wordDist D.alphabet.carrier
          (OsinComponents.vertex (v k C.target) (word k C.target) C.b)
          (OsinComponents.vertex (v k C.target) (word k C.target) C.b') := by
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  have hreindex : ∀ {M : Type} [AddCommMonoid M] (f : Fin d → M),
      ∑ k' : Fin (Fintype.card s), f (e k').1 = ∑ k ∈ s, f k := by
    intro M _ f
    exact (Fintype.sum_equiv e (fun k' => f (e k').1) (fun x : s => f x.1) fun _ => rfl).trans
      (Finset.sum_coe_sort _ _)
  have hbudget' : (∑ k' : Fin (Fintype.card s), sideCount (e k').1) ≤ K * n :=
    (hreindex sideCount).trans_le hbudget
  have hzero : ∑ k ∈ s, classWordLength (word k) (sideCount k) (A k) =
      ∑ k : Fin d, classWordLength (word k) (sideCount k) (A k) :=
    Finset.sum_subset (Finset.subset_univ s) fun k _ hk =>
      classWordLength_eq_zero_of_forall_not_mem (word k) (sideCount k) (A k)
        fun i hi hiA => hk (hs k i hi hiA)
  have hdense' : (n : ℝ) * Real.sqrt (rho : ℝ) ≤
      ∑ k' : Fin (Fintype.card s),
        classWordLength (word (e k').1) (sideCount (e k').1) (A (e k').1) :=
    hdense.trans_eq ((hreindex fun k => classWordLength (word k) (sideCount k) (A k)).trans
      hzero).symm
  obtain ⟨k', C, hback, hlongS, hlongT⟩ := hmetric n (Fintype.card s) hn
    (fun k' => sideCount (e k').1) (fun k' => v (e k').1) (fun k' => word (e k').1)
    (fun k' => A (e k').1) (fun k' => B (e k').1) hbudget' (fun k' => hclosed (e k').1)
    (fun k' i hi => hstep (e k').1 i hi) (fun k' i hi hmem => hqg (e k').1 i hi hmem)
    (fun k' i hi hnot => hshort (e k').1 i hi hnot) hdense'
  exact ⟨(e k').1, C, hback, hlongS, hlongT⟩

namespace OsinLemma94ClassPolygons

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- **The contradiction at fixed parameters, at two thresholds.**  As `unbound_lt_of_classes`, with the
metric half at `epsC ≤ epsL` and the cases refuting the pairs with connectors below `epsC` and segments
above `epsL`. -/
theorem unbound_lt_of_classesTwo (Q : OsinLemma94ClassPolygons P) {K M L rho rhom epsC epsL : ℕ}
    (hcells : 0 < Delta.rCellCount) (hbudget : Q.ClassBudget K) (hcovers : Q.ClassCovers M L)
    (hM : 0 < M) (hrhom : 4 * M * M * rhom ≤ rho) (hL : 4 * L * L ≤ rho) (hepsL : eps ≤ epsL)
    (hmetric : ∀ rho' : ℕ, rhom ≤ rho' →
      OsinLemma94DensePolygonsAntiparallelTwo (symmetricLabelAlphabet D) lambda (c + 2) epsC epsL
        rho' K)
    (hcases : ∀ (k : Fin P.count) (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k)
      (Q.word k) (Q.classCount k) (Q.relatorClasses k) (Q.longClasses k) epsC),
        C.b' < C.b →
        epsL < WordMetric.wordDist (symmetricLabelAlphabet D).alphabet.carrier
          (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a)
          (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a') →
        epsL < WordMetric.wordDist (symmetricLabelAlphabet D).alphabet.carrier
          (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b)
          (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b') → False) :
    (∑ i : Fin S.diagram.rCellCount,
        ((RegionCandidate.unboundDarts S.family i).card : ℝ)) <
      (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ) := by
  by_contra hge
  have hdense := Q.dense_of_classCovers hcovers hM hL (not_lt.mp hge)
  have hle : rhom ≤ rho / (4 * M * M) := by
    refine (Nat.le_div_iff_mul_le (Nat.mul_pos (Nat.mul_pos (by norm_num) hM) hM)).mpr ?_
    rw [Nat.mul_comm]
    exact hrhom
  obtain ⟨k, C, hback, hlongS, hlongT⟩ :=
    OsinLemma94DensePolygonsAntiparallelTwo.exists_of_budget_on
      (hmetric (rho / (4 * M * M)) hle) hcells Q.classCount Q.corner Q.word Q.relatorClasses
      Q.longClasses Q.budgetPolygons Q.mem_budgetPolygons hbudget Q.corner_closed
      (fun k i _ => Q.corner_step k i) Q.quasiGeodesic_of_mem
      (fun k i hi hnot => ⟨(Q.short_of_not_mem k i hi hnot).1,
        (Q.short_of_not_mem k i hi hnot).2.trans hepsL⟩) hdense
  exact hcases k C hback hlongS hlongT

end OsinLemma94ClassPolygons

/-- **Cases 1 and 2 of Lemma 9.4 on class words, at two thresholds (residual).**  The prefix of
`OsinLemma94ClassCasesInput`; the pairs have connectors below `ε − B` and segments above `ε + B`, with
`B = ⌈(c + 2) / λ⌉₊`. -/
def OsinLemma94ClassCasesTwoThresholdInput : Prop :=
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
                        (Q.classCount k) (Q.relatorClasses k) (Q.longClasses k)
                        (eps - ⌈(c + 2) / lambda⌉₊)),
                      eps + ⌈(c + 2) / lambda⌉₊ < WordMetric.wordDist
                          (symmetricLabelAlphabet D).alphabet.carrier
                          (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a)
                          (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a') →
                      eps + ⌈(c + 2) / lambda⌉₊ < WordMetric.wordDist
                          (symmetricLabelAlphabet D).alphabet.carrier
                          (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b)
                          (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b') →
                      C.b' < C.b → False

/-- **Osin's Lemma 9.4 from the class count and the class-word cases at two thresholds.**  The metric
half runs at `ε − B` and `ε + B`, so `ε₀` exceeds its threshold by `B`. -/
theorem osinLemma94Section_of_classCountTwoThreshold
    (hcount : OsinLemma94ClassCountInput.{u, w, v})
    (hcases : OsinLemma94ClassCasesTwoThresholdInput.{u, w, v}) :
    OsinLemma94SectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps1, hcountE⟩ := hcount D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  have hhyperE : ∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic (symmetricLabelAlphabet D).alphabet.carrier delta := by
    rw [symmetricLabelAlphabet.carrier_eq]
    exact hhyper
  obtain ⟨eps2, hmetricE⟩ :=
    osinLemma94AntiparallelMetricTwo (symmetricLabelAlphabet D) hhyperE lambda (c + 2) hlambda
      (by linarith)
  obtain ⟨eps3, hrealEps⟩ :=
    osinLemma94PolygonRealizationInput D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps4, hcasesEps⟩ := hcases D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max eps1 (max (eps2 + ⌈(c + 2) / lambda⌉₊) (max eps3 eps4)), fun eps heps => ?_⟩
  simp only [max_le_iff] at heps
  obtain ⟨he1, he2, he3, he4⟩ := heps
  obtain ⟨K, M, L, hM, rho1, hrho1, hcountEps⟩ := hcountE eps he1
  obtain ⟨rho2, _, hmetricEps⟩ := hmetricE (eps - ⌈(c + 2) / lambda⌉₊) (by omega)
    (eps + ⌈(c + 2) / lambda⌉₊) (by omega) K
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
  exact Q.unbound_lt_of_classesTwo hcells hbudget hcovers hM hr2 hrL (Nat.le_add_right _ _)
    hmetricEps
    (fun k C hback hlongS hlongT =>
      hcasesRho rho hr4 W hW Delta cuts hleast hcells hbelow T hTcard' hTmin P hP Q k C hlongS
        hlongT hback)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94DensePolygonsAntiparallelTwo.exists_of_budget_on
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.unbound_lt_of_classesTwo
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94Section_of_classCountTwoThreshold
