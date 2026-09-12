import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94RunInput
import GroupApproximation.GGT.VanKampen.Estimating.UnboundWordPolygonMonotone
import GroupApproximation.GGT.CayleyFourPointBridge
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4 from the run input

"Assume that `S ≥ n √ρ`."  Since "`∑ n_i ≤ 53 n`" (Lemma 9.3), some component
satisfies (37), `S_i ≥ n_i √ρ / 60`.  Its polygon is dense, so Lemma 3.7 gives an
`ε`-close pair of long subsegments (39), and Cases 1 and 2 refute the pair.  "Hence
`S < n √ρ`."  (Osin, math/0411039v3, proof of Lemma 9.4.)

* `OsinLemma94ComponentPolygons.arcCount_sum_le`: Lemma 9.3's arithmetic.  The Euler
  count `|M| ≤ 3(n + r − 1)` is a binder of the statement, and with `1 ≤ n`, `r ≤ 4`
  it gives `4|M| + n + r ≤ 53 n`.
* `OsinLemma94ComponentPolygons.unbound_lt`: the contradiction at fixed parameters.
  The density selection (37) and Lemma 3.7 are the metric conclusion of
  `UnboundEstimate.unboundComponentWordPolygonsMonotone`.
* `osinLemma94Section_of_runInput`: the monotone thresholds, as maxima of the
  producer's and the metric theorem's, with `Γ(G, A)` hyperbolic by
  `isHyperbolicSpace_cayley_of_fourPoint`.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

namespace OsinLemma94ComponentPolygons

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- **Lemma 9.3**, "`∑ n_i ≤ 53 n`": `e ≤ 3(v − 1) ≤ 12 n`, so
`#A1 + #A2 ≤ 2|M| + n + r ≤ 29 n` and `#A3 ≤ 2|M| ≤ 24 n`. -/
theorem arcCount_sum_le (P : OsinLemma94ComponentPolygons D lambda c eps S)
    (hcells : 0 < Delta.rCellCount)
    (hcard : S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1)) :
    ∑ k, P.arcCount k ≤ 53 * Delta.rCellCount := by
  have hbudget := P.arc_budget
  have hr := cuts.count_le
  omega

/-- **Lemma 9.4 at fixed parameters.**  If the component polygons carried
`∑ unbound ≥ n √ρ`, the metric conclusion would produce a connector pair in one of
them, which `no_connector` refutes. -/
theorem unbound_lt (P : OsinLemma94ComponentPolygons D lambda c eps S) {rho : ℕ}
    (hcells : 0 < Delta.rCellCount)
    (hcard : S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1))
    (hmetric : ∀ (n d : ℕ), 0 < n →
      ∀ (arcCount sideCount : Fin d → ℕ) (v : Fin d → ℕ → G)
        (word : Fin d → ℕ → List (RelLetter G Lambda)) (A B : Fin d → Set ℕ),
        (∑ k : Fin d, arcCount k) ≤ 53 * n →
        (∀ k, sideCount k ≤ 4 * arcCount k) →
        (∀ k, v k (sideCount k) = v k 0) →
        (∀ k i, i < sideCount k → v k (i + 1) = v k i * RelLetter.listVal (word k i)) →
        (∀ k i, i < sideCount k → i ∈ A k ∨ i ∈ B k →
          IsLambdaCQuasiGeodesicWord D lambda c (word k i)) →
        (∀ k i, i < sideCount k → i ∉ B k →
          HullSC.RelWord.IsAdmissible D (word k i) ∧ (word k i).length ≤ eps) →
        (n : ℝ) * Real.sqrt (rho : ℝ) ≤
          ∑ k : Fin d, classWordLength (word k) (sideCount k) (A k) →
        ∃ k : Fin d,
          Nonempty (WordConnectorPair D (v k) (word k) (sideCount k) (A k) (B k) eps)) :
    (∑ i : Fin S.diagram.rCellCount,
        ((RegionCandidate.unboundDarts S.family i).card : ℝ)) <
      (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ) := by
  by_contra hge
  have hdense := le_trans (not_lt.mp hge) P.covers
  obtain ⟨k, ⟨pair⟩⟩ := hmetric Delta.rCellCount P.count hcells P.arcCount P.sideCount
    P.corner P.word P.relatorSides P.longSides (P.arcCount_sum_le hcells hcard)
    P.side_le P.closed P.step P.quasiGeodesic P.short hdense
  exact P.no_connector k pair

end OsinLemma94ComponentPolygons

/-- **Osin's Lemma 9.4 from the run input.**  `OsinLemma94SectionStatement`, verbatim,
from `OsinLemma94RunInput` and the proved metric theorem. -/
theorem osinLemma94Section_of_runInput (hrun : OsinLemma94RunInput.{u, w, v}) :
    OsinLemma94SectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨delta, hdelta⟩ := hhyper
  obtain ⟨_, _, eps1, hmetric⟩ :=
    unboundComponentWordPolygonsMonotone G Lambda D (delta : ℝ) lambda c mu
      (isHyperbolicSpace_cayley_of_fourPoint D.alphabet hdelta) (by positivity)
      hlambda hc hmu
  obtain ⟨eps2, hproducer⟩ :=
    hrun D ⟨delta, hdelta⟩ lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max eps1 eps2, fun eps heps => ?_⟩
  obtain ⟨rho1, hrho1, hmetricEps⟩ := hmetric eps (le_trans (le_max_left _ _) heps)
  obtain ⟨rho2, _, hproducerEps⟩ := hproducer eps (le_trans (le_max_right _ _) heps)
  refine ⟨max rho1 rho2, lt_of_lt_of_le hrho1 (le_max_left _ _), fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast hcells S hcard
  obtain ⟨P⟩ := hproducerEps rho (le_trans (le_max_right _ _) hrho) W hW Delta cuts
    hleast hcells S hcard
  exact P.unbound_lt hcells hcard (hmetricEps rho (le_trans (le_max_left _ _) hrho)).2

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ComponentPolygons.arcCount_sum_le
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ComponentPolygons.unbound_lt
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94Section_of_runInput

end GroupApproximation.GGT.VanKampen
