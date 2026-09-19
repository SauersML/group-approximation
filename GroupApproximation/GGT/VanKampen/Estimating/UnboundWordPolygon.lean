import GroupApproximation.GGT.VanKampen.WordPolygonReplacement
import GroupApproximation.GGT.VanKampen.Estimating.UnboundPolygonGeometry

/-!
# The complete metric input to the unbound-arc argument

The ambient constants determine a Morse radius, epsilon, and a uniform rho
threshold. A dense cyclic word polygon then supplies two distinct original
sides with long subsegments and short connectors. Its geodesic replacement,
both class-length estimates, and all Morse endpoint witnesses are constructed
in the proof. Only the two retained classes must be quasi-geodesic; the short
connector class needs admissibility and its length bound.

This is the metric part of Osin's Appendix Lemma 9.4. The complementary
regions and the surgery contradicting minimality are separate obligations.
-/

namespace GroupApproximation.GGT.VanKampen.UnboundEstimate

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Olshanskii
open CayleyGeodesicModel

universe u w

/-- Two distinct original word sides, with short cross-connectors and long
segments between their chosen indexed endpoints. -/
def WordSidePair {G : Type u} [Group G] {Lambda : Type w}
    (D : RelGenSet G Lambda) (v : ℕ → G) (word : ℕ → List (RelLetter G Lambda))
    (n : ℕ) (A B : Set ℕ) (eps : ℕ) : Prop :=
  ∃ i < n, ∃ j < n, i ∈ A ∧ j ∈ B ∧ i ≠ j ∧
    ∃ a ≤ (word i).length, ∃ a' ≤ (word i).length,
      ∃ b ≤ (word j).length, ∃ b' ≤ (word j).length,
        wordDist D.alphabet.carrier (OsinComponents.vertex (v i) (word i) a)
          (OsinComponents.vertex (v j) (word j) b) < eps ∧
        wordDist D.alphabet.carrier (OsinComponents.vertex (v i) (word i) a')
          (OsinComponents.vertex (v j) (word j) b') < eps ∧
        eps < wordDist D.alphabet.carrier (OsinComponents.vertex (v i) (word i) a)
          (OsinComponents.vertex (v i) (word i) a') ∧
        eps < wordDist D.alphabet.carrier (OsinComponents.vertex (v j) (word j) b)
          (OsinComponents.vertex (v j) (word j) b')

/-- Simultaneous geometric parameters and the original-word conclusion.
There is no supplied Morse radius, replacement polygon, or proximity field. -/
def UnboundWordPolygonStatement : Prop :=
  ∀ (G : Type u) [Group G] (Lambda : Type w) (D : RelGenSet G Lambda)
    (δ lambda c mu : ℝ),
    IsHyperbolicSpace δ (Cayley D.alphabet) → 0 ≤ δ →
    0 < lambda → 0 ≤ c → 0 < mu →
    ∃ kappa : ℝ, 0 ≤ kappa ∧ ∃ eps rho0 : ℕ, 0 < rho0 ∧
      ∀ rho : ℕ, rho0 ≤ rho →
        OsinUnboundScale lambda c mu kappa (12 * ((δ + 6) + 1))
          (100000 * ((δ + 6) + 1)) eps rho ∧
        ∀ (n : ℕ) (v : ℕ → G) (word : ℕ → List (RelLetter G Lambda)) (A B : Set ℕ),
          v n = v 0 →
          (∀ i < n, v (i + 1) = v i * RelLetter.listVal (word i)) →
          (∀ i < n, i ∈ A ∨ i ∈ B → IsLambdaCQuasiGeodesicWord D lambda c (word i)) →
          (∀ i < n, i ∉ B → HullSC.RelWord.IsAdmissible D (word i) ∧ (word i).length ≤ eps) →
          (n : ℝ) * Real.sqrt (rho : ℝ) / 240 < classWordLength word n A →
          WordSidePair D v word n A B eps

/-- The metric conclusion used to shorten cutting paths or create a new
contiguity region follows from the actual word polygon. -/
theorem unboundWordPolygon : UnboundWordPolygonStatement.{u, w} := by
  intro G _ Lambda D δ lambda c mu hδ hδ0 hlambda hc hmu
  obtain ⟨kappa, hkappa, hmorse⟩ := exists_word_replacement_morse D lambda c hlambda hδ hδ0
  obtain ⟨eps, rho0, hrho0, hscale⟩ :=
    exists_polygonScale_parameters (δ + 6) lambda c mu kappa hlambda hmu
  refine ⟨kappa, hkappa, eps, rho0, hrho0, ?_⟩
  intro rho hrho
  have scale := hscale rho hrho
  refine ⟨scale, ?_⟩
  intro n v word A B hclose hends hquasi hshort hdense
  obtain ⟨sides, hpoly⟩ := exists_geodesic_replacement_polygon D v n hclose
  have hfirst := replacement_first_class_dense D v word hends A hlambda hc
    (fun i hi hiA => hquasi i hi (Or.inl hiA)) hdense
  have hsmall := replacement_short_class_le D v word hends B hshort
  let arc : ℕ → ℕ → PointQuot D.alphabet :=
    fun i k => vertexQuot D.alphabet (OsinComponents.vertex (v i) (word i) k)
  have hnear : ∀ i < n, i ∈ A ∨ i ∈ B →
      ∀ t ∈ Set.Icc (0 : ℝ)
        (dist (vertexQuot D.alphabet (v i)) (vertexQuot D.alphabet (v (i + 1)))),
      ∃ k ≤ (word i).length, dist (sides i t) (arc i k) ≤ kappa := by
    intro i hi hiAB t ht
    obtain ⟨hgeo, hz, he⟩ := hpoly.1 i (Nat.zero_le i) (by simpa using hi)
    have hgeo' : IsGeodesicSegment (sides i) 0
        (dist (vertexQuot D.alphabet (v i))
          (vertexQuot D.alphabet (v i * RelLetter.listVal (word i)))) := by
      simpa only [hends i hi] using hgeo
    have he' : sides i (dist (vertexQuot D.alphabet (v i))
        (vertexQuot D.alphabet (v i * RelLetter.listVal (word i)))) =
      vertexQuot D.alphabet (v i * RelLetter.listVal (word i)) := by
      simpa only [hends i hi] using he
    have ht' : t ∈ Set.Icc (0 : ℝ)
        (dist (vertexQuot D.alphabet (v i))
          (vertexQuot D.alphabet (v i * RelLetter.listVal (word i)))) := by
      simpa only [hends i hi] using ht
    exact (hmorse (word i) (hquasi i hi hiAB) (v i) (sides i) hgeo' hz he').2 t ht'
  have hreal : IsHyperbolicSpace (δ + 6) (PointQuot D.alphabet) :=
    isHyperbolicSpace_pointQuot (isHyperbolicSpace_point D.alphabet hδ)
  obtain ⟨i, hi, j, hj, hiA, hjB, hne, a, ha, a', ha', b, hb, b', hb', hcross,
    hcross', hlong, hlong'⟩ := scale.exists_originalArcPair_of_class_near hreal
      (by linarith) (isGeodesicRealisationQuot D.alphabet) hpoly A B arc
      (fun i => (word i).length) hnear hfirst hsmall
  refine ⟨i, hi, j, hj, hiA, hjB, hne, a, ha, a', ha', b, hb, b', hb', ?_, ?_, ?_, ?_⟩
  · simpa only [arc, dist_vertexQuot, Nat.cast_lt] using hcross
  · simpa only [arc, dist_vertexQuot, Nat.cast_lt] using hcross'
  · simpa only [arc, dist_vertexQuot, Nat.cast_lt] using hlong
  · simpa only [arc, dist_vertexQuot, Nat.cast_lt] using hlong'

end GroupApproximation.GGT.VanKampen.UnboundEstimate

#audit_closed_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.unboundWordPolygon
