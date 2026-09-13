import GroupApproximation.GGT.VanKampen.Estimating.UnboundOrientedWordConnectors
import GroupApproximation.GGT.VanKampen.WordPolygonReplacement
import GroupApproximation.GGT.OlshanskiiOrientedThreeClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# The oriented metric part of Osin's Appendix Lemma 9.4

Osin, *Small cancellations over relatively hyperbolic groups and embedding
theorems*, arXiv:math/0411039v3, Appendix, proof of Lemma 9.4.
`unboundWordPolygonMonotone` gives a `WordSidePair`, which leaves the order of the
target indices open.  Case 1 of the proof contradicts only the antiparallel pair
`b' < b` (`UnboundOrientedWordConnectors`).  This file proves the same theorem with
that orientation, from the same ingredients and the oriented three-class lemma of
`OlshanskiiOrientedThreeClasses`.

* `OsinUnboundScale.exists_orientedPolygonPair`: the two component-length estimates
  give an `OrientedClassPair` at the segment length of the scale.  It is
  `exists_polygonPair` with `exists_orientedClassPair_of_aggregate_all`.
* `unboundOrientedWordPolygonMonotone`: `UnboundWordPolygonMonotoneStatement` with the
  conclusion `OrientedWordSidePair`, at the same monotone thresholds.  The Morse radius
  comes from `exists_word_replacement_morse_monotone`, and
  `OsinUnboundScale.orientedWordSidePair_of_orientedClassPair` moves the pair to
  original vertex indices.
-/

namespace GroupApproximation.GGT.VanKampen.UnboundEstimate

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Olshanskii
open CayleyGeodesicModel

universe u w v

/-- The two component-length estimates imply an antiparallel pair of long geodesic
segments, at the same epsilon and rho as the budget estimate. -/
theorem OsinUnboundScale.exists_orientedPolygonPair
    {X : Type v} [PseudoMetricSpace X] {δ lambda c mu kappa : ℝ}
    {eps rho : ℕ}
    (scale : OsinUnboundScale lambda c mu kappa (12 * (δ + 1))
      (100000 * (δ + 1)) eps rho)
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    {n : ℕ} {vs : ℕ → X} {sides : ℕ → ℝ → X}
    (hpoly : IsClosedPolygonAt vs sides 0 n) (A B : Set ℕ)
    (hfirst : (lambda * Real.sqrt (rho : ℝ) / 240 - c) * n < classLength vs n A)
    (hshort : classLength vs n Bᶜ ≤ (eps : ℝ) * n) :
    OrientedClassPair vs sides n A B
      ((lambda * Real.sqrt (rho : ℝ) / 240 - c) / 1000) (12 * (δ + 1)) := by
  have hn : 0 < n := by
    by_contra hbad
    have hn0 : n = 0 := by omega
    simp [hn0, classLength] at hfirst
  have ha := lt_of_le_of_lt (le_max_right _ _) scale.density_large
  have heps := lt_of_le_of_lt (le_max_left _ _) scale.density_large
  apply exists_orientedClassPair_of_aggregate_all hδ hδ0 hgeo hpoly A B (le_of_lt ha) hfirst
  have h := side_total_lt_oneThousandth hn hshort heps
  convert h using 1
  ring

/-- The metric word-polygon conclusion in the antiparallel configuration, with
monotone thresholds: every `eps` above one closeness bound works, with a `rho`
threshold chosen after it, and the pair has `a < a'` and `b' < b`. -/
def UnboundOrientedWordPolygonMonotoneStatement : Prop :=
  ∀ (G : Type u) [Group G] (Lambda : Type w) (D : RelGenSet G Lambda)
    (δ lambda c mu : ℝ),
    IsHyperbolicSpace δ (Cayley D.alphabet) → 0 ≤ δ →
    0 < lambda → 0 ≤ c → 0 < mu →
    ∃ kappa : ℝ, 0 ≤ kappa ∧ ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
      ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
        OsinUnboundScale lambda c mu kappa (12 * ((δ + 6) + 1))
          (100000 * ((δ + 6) + 1)) eps rho ∧
        ∀ (n : ℕ) (v : ℕ → G) (word : ℕ → List (RelLetter G Lambda)) (A B : Set ℕ),
          v n = v 0 →
          (∀ i < n, v (i + 1) = v i * RelLetter.listVal (word i)) →
          (∀ i < n, i ∈ A ∨ i ∈ B → IsLambdaCQuasiGeodesicWord D lambda c (word i)) →
          (∀ i < n, i ∉ B → HullSC.RelWord.IsAdmissible D (word i) ∧ (word i).length ≤ eps) →
          (n : ℝ) * Real.sqrt (rho : ℝ) / 240 < classWordLength word n A →
          OrientedWordSidePair D v word n A B eps

/-- The metric part of Lemma 9.4 in the antiparallel configuration holds at every `eps`
above the closeness bound `12 ((δ + 6) + 1) + 2 kappa`, each with its own uniform `rho`
threshold. -/
theorem unboundOrientedWordPolygonMonotone :
    UnboundOrientedWordPolygonMonotoneStatement.{u, w} := by
  intro G _ Lambda D δ lambda c mu hδ hδ0 hlambda hc hmu
  obtain ⟨kappa, hkappa, hmorse, -⟩ :=
    exists_word_replacement_morse_monotone D lambda c hlambda hδ hδ0
  obtain ⟨eps0, heps0⟩ := exists_nat_gt (12 * ((δ + 6) + 1) + 2 * kappa)
  refine ⟨kappa, hkappa, eps0, ?_⟩
  intro eps heps
  have hepsReal : 12 * ((δ + 6) + 1) + 2 * kappa < (eps : ℝ) :=
    lt_of_lt_of_le heps0 (by exact_mod_cast heps)
  obtain ⟨rho0, hrho0, hscale⟩ := exists_osinUnboundScale_after_epsilon lambda c mu kappa
    (12 * ((δ + 6) + 1)) (100000 * ((δ + 6) + 1)) hlambda hmu eps hepsReal
  refine ⟨rho0, hrho0, ?_⟩
  intro rho hrho
  have scale := hscale rho hrho
  refine ⟨scale, ?_⟩
  intro n v word A B hclose hends hquasi hshort hdense
  obtain ⟨sides, hpoly⟩ := exists_geodesic_replacement_polygon D v n hclose
  have hfirst := replacement_first_class_dense D v word hends A hlambda hc
    (fun i hi hiA => hquasi i hi (Or.inl hiA)) hdense
  have hsmall := replacement_short_class_le D v word hends B hshort
  have hreal : IsHyperbolicSpace (δ + 6) (PointQuot D.alphabet) :=
    isHyperbolicSpace_pointQuot (isHyperbolicSpace_point D.alphabet hδ)
  have hpair := scale.exists_orientedPolygonPair hreal (by linarith)
    (isGeodesicRealisationQuot D.alphabet) hpoly A B hfirst hsmall
  exact scale.orientedWordSidePair_of_orientedClassPair hreal (by linarith) hmorse hpoly
    hends A B hquasi hpair

end GroupApproximation.GGT.VanKampen.UnboundEstimate

#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.OsinUnboundScale.exists_orientedPolygonPair
#audit_closed_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.unboundOrientedWordPolygonMonotone
