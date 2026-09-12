import GroupApproximation.GGT.VanKampen.Estimating.UnboundComponentWordPolygons
import GroupApproximation.Meta.AxiomGuard

/-!
# Monotone thresholds for the metric part of Osin's Appendix Lemma 9.4

`unboundWordPolygon` and `unboundComponentWordPolygons` choose one `eps` and a
`rho` threshold after it.  The induction of Osin's Appendix Lemma 9.7
(arXiv:math/0411039v3) combines the unbound-arc estimate with other estimates
that need `eps` and `rho` large for their own reasons (Lemma 4.3 pieces, the
short contiguity arcs of part (a)), so the unbound estimate must hold for every
larger `eps`, each with its own `rho` threshold.

Osin's two numerical choices are monotone in exactly this way: equation (36),
`c1 + 2 * kappa < eps`, survives enlarging `eps`, and
`exists_osinUnboundScale_after_epsilon` already supplies a uniform `rho`
threshold for any `eps` above the closeness bound.  The Morse radius `kappa` and
the polygon constants `c1 = 12 ((delta + 6) + 1)`, `c2 = 100000 ((delta + 6) + 1)`
do not depend on `eps`.  So this file restates both metric theorems with the
quantifiers `∃ eps0, ∀ eps ≥ eps0, ∃ rho0, ∀ rho ≥ rho0` and reproves them from
the same landed ingredients.
-/

namespace GroupApproximation.GGT.VanKampen.UnboundEstimate

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Olshanskii
open CayleyGeodesicModel

universe u w

/-- The metric word-polygon conclusion with monotone thresholds: every `eps`
above one closeness bound works, with a `rho` threshold chosen after it. -/
def UnboundWordPolygonMonotoneStatement : Prop :=
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
          WordSidePair D v word n A B eps

/-- The metric part of Lemma 9.4 holds at every `eps` above the closeness bound
`12 ((delta + 6) + 1) + 2 kappa`, each with its own uniform `rho` threshold. -/
theorem unboundWordPolygonMonotone : UnboundWordPolygonMonotoneStatement.{u, w} := by
  intro G _ Lambda D δ lambda c mu hδ hδ0 hlambda hc hmu
  obtain ⟨kappa, hkappa, hmorse⟩ := exists_word_replacement_morse D lambda c hlambda hδ hδ0
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

/-- The component-family form with monotone thresholds: the `53 n` arc budget
and the fourfold cutting bound select a dense polygon, which carries an actual
connector pair, at every `eps` above the closeness bound. -/
def UnboundComponentWordPolygonsMonotoneStatement : Prop :=
  ∀ (G : Type u) [Group G] (Lambda : Type w) (D : RelGenSet G Lambda)
    (δ lambda c mu : ℝ),
    IsHyperbolicSpace δ (Cayley D.alphabet) → 0 ≤ δ →
    0 < lambda → 0 ≤ c → 0 < mu →
    ∃ kappa : ℝ, 0 ≤ kappa ∧ ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
      ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
        OsinUnboundScale lambda c mu kappa (12 * ((δ + 6) + 1))
          (100000 * ((δ + 6) + 1)) eps rho ∧
        ∀ (n d : ℕ), 0 < n →
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
              Nonempty (WordConnectorPair D (v k) (word k) (sideCount k) (A k) (B k) eps)

theorem unboundComponentWordPolygonsMonotone :
    UnboundComponentWordPolygonsMonotoneStatement.{u, w} := by
  intro G _ Lambda D δ lambda c mu hδ hδ0 hlambda hc hmu
  obtain ⟨kappa, hkappa, eps0, hpolygon⟩ :=
    unboundWordPolygonMonotone G Lambda D δ lambda c mu hδ hδ0 hlambda hc hmu
  refine ⟨kappa, hkappa, eps0, ?_⟩
  intro eps heps
  obtain ⟨rho0, hrho0, hpoly⟩ := hpolygon eps heps
  refine ⟨rho0, hrho0, ?_⟩
  intro rho hrho
  obtain ⟨scale, hpairs⟩ := hpoly rho hrho
  refine ⟨scale, ?_⟩
  intro n d hn arcCount sideCount v word A B hcount hsides hclose hends hquasi hshort htotal
  have hsqrt : 0 < Real.sqrt (rho : ℝ) := Real.sqrt_pos.mpr
    (by exact_mod_cast lt_of_lt_of_le hrho0 hrho)
  obtain ⟨k, hdense⟩ := exists_component_gt_twoForty n hn (Real.sqrt (rho : ℝ)) hsqrt
    arcCount sideCount (fun k => classWordLength (word k) (sideCount k) (A k))
    hcount hsides htotal
  have pair := hpairs (sideCount k) (v k) (word k) (A k) (B k) (hclose k)
    (hends k) (hquasi k) (hshort k) hdense
  exact ⟨k, pair.exists_connectors (fun i hi hiAB => (hquasi k i hi hiAB).1)⟩

end GroupApproximation.GGT.VanKampen.UnboundEstimate

#audit_closed_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.unboundWordPolygonMonotone
#audit_closed_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.unboundComponentWordPolygonsMonotone
