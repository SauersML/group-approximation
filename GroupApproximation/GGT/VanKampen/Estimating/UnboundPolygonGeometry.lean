import GroupApproximation.GGT.OlshanskiiThreeClasses
import GroupApproximation.GGT.VanKampen.Estimating.UnboundParameters
import GroupApproximation.GGT.CayleyGeodesicRealisation

/-!
# The actual polygon constants in Osin's unbound argument

Ol'shanskii's full three-class theorem now supplies `c1` and `c2`. The
existing numerical scale choice therefore produces epsilon and rho from
the hyperbolicity constant and a Morse radius, with no polygon-constant
oracle. The density and short-side estimates give the actual long pair.

For Cayley graphs this is applied in the proved geodesic metric realization,
whose hyperbolicity constant is the vertex constant plus six. The vertex
set itself is not assumed to be a geodesic space.
-/

namespace GroupApproximation.GGT.VanKampen.UnboundEstimate

open GroupApproximation.HullGeometry
open GroupApproximation.Olshanskii

universe v u

/-- The source's constants now come from the proved polygon theorem. The
Morse radius remains explicit at this numerical interface. -/
theorem exists_polygonScale_parameters (δ lambda c mu kappa : ℝ)
    (hlambda : 0 < lambda) (hmu : 0 < mu) :
    ∃ eps rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
      OsinUnboundScale lambda c mu kappa (12 * (δ + 1))
        (100000 * (δ + 1)) eps rho :=
  exists_osinUnboundScale_parameters lambda c mu kappa (12 * (δ + 1))
    (100000 * (δ + 1)) hlambda hmu

/-- The two component-length estimates imply a genuine pair of long
geodesic segments, at the same epsilon and rho as the budget estimate. -/
theorem OsinUnboundScale.exists_polygonPair
    {X : Type v} [PseudoMetricSpace X] {δ lambda c mu kappa : ℝ}
    {eps rho : ℕ}
    (scale : OsinUnboundScale lambda c mu kappa (12 * (δ + 1))
      (100000 * (δ + 1)) eps rho)
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    {n : ℕ} {vs : ℕ → X} {sides : ℕ → ℝ → X}
    (hpoly : IsClosedPolygonAt vs sides 0 n) (A B : Set ℕ)
    (hfirst : (lambda * Real.sqrt (rho : ℝ) / 240 - c) * n < classLength vs n A)
    (hshort : classLength vs n Bᶜ ≤ (eps : ℝ) * n) :
    ClassPair vs sides n A B
      ((lambda * Real.sqrt (rho : ℝ) / 240 - c) / 1000) (12 * (δ + 1)) := by
  have hn : 0 < n := by
    by_contra hbad
    have hn0 : n = 0 := by omega
    simp [hn0, classLength] at hfirst
  have ha := lt_of_le_of_lt (le_max_right _ _) scale.density_large
  have heps := lt_of_le_of_lt (le_max_left _ _) scale.density_large
  apply exists_classPair_of_aggregate_all hδ hδ0 hgeo hpoly A B (le_of_lt ha) hfirst
  have h := side_total_lt_oneThousandth hn hshort heps
  convert h using 1
  ring

/-- Application on the actual Cayley realization. Its extra six units of
hyperbolicity are included before epsilon and rho are chosen. -/
theorem OsinUnboundScale.exists_cayleyPolygonPair
    {G : Type u} [Group G] (alphabet : Manuscript.NonMF.TorsionFree.Alphabet G)
    {δ lambda c mu kappa : ℝ} {eps rho : ℕ}
    (hδ : IsHyperbolicSpace δ (Manuscript.NonMF.TorsionFree.Cayley alphabet))
    (hδ0 : 0 ≤ δ)
    (scale : OsinUnboundScale lambda c mu kappa (12 * ((δ + 6) + 1))
      (100000 * ((δ + 6) + 1)) eps rho)
    {n : ℕ} {vs : ℕ → CayleyGeodesicModel.PointQuot alphabet}
    {sides : ℕ → ℝ → CayleyGeodesicModel.PointQuot alphabet}
    (hpoly : IsClosedPolygonAt vs sides 0 n) (A B : Set ℕ)
    (hfirst : (lambda * Real.sqrt (rho : ℝ) / 240 - c) * n < classLength vs n A)
    (hshort : classLength vs n Bᶜ ≤ (eps : ℝ) * n) :
    ClassPair vs sides n A B
      ((lambda * Real.sqrt (rho : ℝ) / 240 - c) / 1000) (12 * ((δ + 6) + 1)) := by
  exact scale.exists_polygonPair
    (CayleyGeodesicModel.isHyperbolicSpace_pointQuot
      (CayleyGeodesicModel.isHyperbolicSpace_point alphabet hδ))
    (by linarith) (CayleyGeodesicModel.isGeodesicRealisationQuot alphabet)
    hpoly A B hfirst hshort

/-- Moving four endpoints by at most kappa preserves the strict connector
bound and the strict shortening margin, in both segments. -/
theorem nearby_endpoints_keep_shortening_margin
    {X : Type v} [PseudoMetricSpace X]
    {p p' q q' x x' y y' : X} {β D kappa eps : ℝ}
    (hp : β ≤ dist p p') (hq : β ≤ dist q q')
    (hpq : dist p q ≤ D) (hpq' : dist p' q' ≤ D)
    (hpx : dist p x ≤ kappa) (hpx' : dist p' x' ≤ kappa)
    (hqy : dist q y ≤ kappa) (hqy' : dist q' y' ≤ kappa)
    (hclose : D + 2 * kappa < eps) (hlong : eps < β - 2 * kappa) :
    dist x y < eps ∧ dist x' y' < eps ∧
      eps < dist x x' ∧ eps < dist y y' := by
  have hxp : dist x p ≤ kappa := by simpa only [dist_comm] using hpx
  have hxp' : dist x' p' ≤ kappa := by simpa only [dist_comm] using hpx'
  have hyq' : dist y' q' ≤ kappa := by simpa only [dist_comm] using hqy'
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [dist_triangle x p q, dist_triangle x q y]
  · linarith [dist_triangle x' p' q', dist_triangle x' q' y']
  · linarith [dist_triangle p x x', dist_triangle p x' p']
  · linarith [dist_triangle q y y', dist_triangle q y' q']

/-- A pair supplied by N123 can be transferred to indexed endpoints on the
original quasi-geodesic arcs using Morse proximity on the two retained
classes. Short connector sides need no quasi-geodesic hypothesis. -/
theorem OsinUnboundScale.exists_originalArcPair_of_class_near
    {X : Type v} [PseudoMetricSpace X] {δ lambda c mu kappa : ℝ}
    {eps rho : ℕ}
    (scale : OsinUnboundScale lambda c mu kappa (12 * (δ + 1))
      (100000 * (δ + 1)) eps rho)
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    {n : ℕ} {vs : ℕ → X} {sides : ℕ → ℝ → X}
    (hpoly : IsClosedPolygonAt vs sides 0 n) (A B : Set ℕ)
    (arc : ℕ → ℕ → X) (arcLength : ℕ → ℕ)
    (hnear : ∀ i < n, i ∈ A ∨ i ∈ B → ∀ t ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1))),
      ∃ k ≤ arcLength i, dist (sides i t) (arc i k) ≤ kappa)
    (hfirst : (lambda * Real.sqrt (rho : ℝ) / 240 - c) * n < classLength vs n A)
    (hshort : classLength vs n Bᶜ ≤ (eps : ℝ) * n) :
    ∃ i < n, ∃ j < n, i ∈ A ∧ j ∈ B ∧ i ≠ j ∧
      ∃ u ≤ arcLength i, ∃ u' ≤ arcLength i, ∃ v ≤ arcLength j, ∃ v' ≤ arcLength j,
        dist (arc i u) (arc j v) < eps ∧ dist (arc i u') (arc j v') < eps ∧
          (eps : ℝ) < dist (arc i u) (arc i u') ∧
          (eps : ℝ) < dist (arc j v) (arc j v') := by
  obtain ⟨i, hi, j, hj, hiA, hjB, hne,
    u, hu, u', hu', t, ht, t', ht', hlen, hlen', hc, hc'⟩ :=
      scale.exists_polygonPair hδ hδ0 hgeo hpoly A B hfirst hshort
  obtain ⟨a, ha, hpa⟩ := hnear i hi (Or.inl hiA) u hu
  obtain ⟨a', ha', hpa'⟩ := hnear i hi (Or.inl hiA) u' hu'
  obtain ⟨b, hb, hqb⟩ := hnear j hj (Or.inr hjB) t ht
  obtain ⟨b', hb', hqb'⟩ := hnear j hj (Or.inr hjB) t' ht'
  have hgi := (hpoly.1 i (Nat.zero_le i) (by simpa using hi)).1
  have hgj := (hpoly.1 j (Nat.zero_le j) (by simpa using hj)).1
  have hlenI : (lambda * Real.sqrt (rho : ℝ) / 240 - c) / 1000 ≤
      dist (sides i u) (sides i u') := by
    rw [hgi u hu u' hu', abs_sub_comm]
    exact hlen
  have hlenJ : (lambda * Real.sqrt (rho : ℝ) / 240 - c) / 1000 ≤
      dist (sides j t) (sides j t') := by
    rw [hgj t ht t' ht', abs_sub_comm]
    exact hlen'
  exact ⟨i, hi, j, hj, hiA, hjB, hne, a, ha, a', ha', b, hb, b', hb',
    nearby_endpoints_keep_shortening_margin hlenI hlenJ hc hc'
      hpa hpa' hqb hqb' scale.epsilon_large scale.shortcut_shortens⟩

/-- A pair supplied by N123 can be transferred to indexed endpoints on the
original quasi-geodesic arcs using their Morse proximity. -/
theorem OsinUnboundScale.exists_originalArcPair
    {X : Type v} [PseudoMetricSpace X] {δ lambda c mu kappa : ℝ}
    {eps rho : ℕ}
    (scale : OsinUnboundScale lambda c mu kappa (12 * (δ + 1))
      (100000 * (δ + 1)) eps rho)
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    {n : ℕ} {vs : ℕ → X} {sides : ℕ → ℝ → X}
    (hpoly : IsClosedPolygonAt vs sides 0 n) (A B : Set ℕ)
    (arc : ℕ → ℕ → X) (arcLength : ℕ → ℕ)
    (hnear : ∀ i < n, ∀ t ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1))),
      ∃ k ≤ arcLength i, dist (sides i t) (arc i k) ≤ kappa)
    (hfirst : (lambda * Real.sqrt (rho : ℝ) / 240 - c) * n < classLength vs n A)
    (hshort : classLength vs n Bᶜ ≤ (eps : ℝ) * n) :
    ∃ i < n, ∃ j < n, i ∈ A ∧ j ∈ B ∧ i ≠ j ∧
      ∃ u ≤ arcLength i, ∃ u' ≤ arcLength i, ∃ v ≤ arcLength j, ∃ v' ≤ arcLength j,
        dist (arc i u) (arc j v) < eps ∧ dist (arc i u') (arc j v') < eps ∧
          (eps : ℝ) < dist (arc i u) (arc i u') ∧
          (eps : ℝ) < dist (arc j v) (arc j v') := by
  exact scale.exists_originalArcPair_of_class_near hδ hδ0 hgeo hpoly A B arc arcLength
    (fun i hi _ => hnear i hi) hfirst hshort

end GroupApproximation.GGT.VanKampen.UnboundEstimate

#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.exists_polygonScale_parameters
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.OsinUnboundScale.exists_polygonPair
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.OsinUnboundScale.exists_cayleyPolygonPair
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.OsinUnboundScale.exists_originalArcPair

#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.OsinUnboundScale.exists_originalArcPair_of_class_near
