import GroupApproximation.GGT.CayleyGeodesicRealisation
import GroupApproximation.GGT.CayleyFourPointConverse
import GroupApproximation.GGT.DGOQuasiGeodesicChainHausdorff

/-!
# Morse proximity in the actual Cayley metric realization

The vertex metric embeds isometrically in `PointQuot`. A point on any
geodesic between embedded vertices is close to a between-vertex at its
integer radial parameter. The four-point inequality costs `2 * delta` and
rounding costs one. Composing with the discrete Morse theorem gives a
uniform radius for both directions of proximity, with actual chain indices.
-/

namespace GroupApproximation.GGT.CayleyGeodesicModel

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u
variable {G : Type u} [Group G]

/-- A group vertex in the metric identification of its Cayley graph. -/
def vertexQuot (A : Alphabet G) (g : G) : PointQuot A := mk (vertex A g)

/-- The realization preserves vertex distances exactly. -/
@[simp] theorem dist_vertexQuot (A : Alphabet G) (g h : G) :
    dist (vertexQuot A g) (vertexQuot A h) = (wordDist A.carrier g h : ℝ) := by
  exact pointDist_vertex A g h

theorem gromovProduct_vertexQuot_eq_zero_of_isBetween (A : Alphabet G)
    {x q y : G} (hq : Hyperbolic.IsBetween A.carrier x q y) :
    gromovProduct (vertexQuot A x) (vertexQuot A y) (vertexQuot A q) = 0 := by
  have hsum : (wordDist A.carrier x q : ℝ) + wordDist A.carrier q y =
      wordDist A.carrier x y := by exact_mod_cast hq
  simp only [gromovProduct, dist_vertexQuot,
    wordDist_comm A.symmetricGenerating y q]
  linarith

/-- Every point of a replacement geodesic is near a between-vertex at its
integer radial parameter. The bound is independent of the geodesic length. -/
theorem exists_between_vertex_near_geodesic (A : Alphabet G) {δ : ℝ}
    (hδ : IsHyperbolicSpace δ (PointQuot A)) {x y : G} {f : ℝ → PointQuot A}
    (hf : IsGeodesicSegment f 0 (dist (vertexQuot A x) (vertexQuot A y)))
    (hf0 : f 0 = vertexQuot A x)
    (hf1 : f (dist (vertexQuot A x) (vertexQuot A y)) = vertexQuot A y)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (dist (vertexQuot A x) (vertexQuot A y))) :
    ∃ q : G, Hyperbolic.IsBetween A.carrier x q y ∧
      dist (f t) (vertexQuot A q) ≤ 1 + 2 * δ := by
  have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht.1
  have hround : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have hfloor_le : ⌊t⌋₊ ≤ wordDist A.carrier x y := by
    have h := hfloor.trans ht.2
    rw [dist_vertexQuot] at h
    exact_mod_cast h
  obtain ⟨q, hq, hrad⟩ := Hyperbolic.exists_isBetween A.symmetricGenerating x y hfloor_le
  have hsum : dist (vertexQuot A x) (vertexQuot A q) +
      dist (vertexQuot A q) (vertexQuot A y) =
        dist (vertexQuot A x) (vertexQuot A y) := by
    simp only [dist_vertexQuot]
    exact_mod_cast hq
  have hradR : dist (vertexQuot A x) (vertexQuot A q) = (⌊t⌋₊ : ℝ) := by
    rw [dist_vertexQuot, hrad]
  have hfloor0 : (0 : ℝ) ≤ (⌊t⌋₊ : ℝ) := by positivity
  have hfloorM := hfloor.trans ht.2
  have hprojection := dist_le_gromovProduct_add hδ hf hf0 hf1 (vertexQuot A q)
    hfloor0 hfloorM (by rw [dist_comm (vertexQuot A y) (vertexQuot A q)]; linarith)
  rw [gromovProduct_vertexQuot_eq_zero_of_isBetween A hq, zero_add] at hprojection
  have hparameter : dist (f t) (f (⌊t⌋₊ : ℝ)) ≤ 1 := by
    rw [hf t ht (⌊t⌋₊ : ℝ) ⟨hfloor0, hfloorM⟩, abs_of_nonneg (by linarith)]
    linarith
  refine ⟨q, hq, ?_⟩
  have htriangle := dist_triangle (f t) (f (⌊t⌋₊ : ℝ)) (vertexQuot A q)
  rw [dist_comm (f (⌊t⌋₊ : ℝ)) (vertexQuot A q)] at htriangle
  linarith

/-- One radius works for all quasi-geodesic chains and every geodesic
replacement of their endpoints, in both directions. -/
theorem exists_chain_realization_hausdorff_bound (A : Alphabet G)
    (mu : ℝ) (b : ℕ) {δ : ℝ} (hmu : 0 < mu)
    (hδ : IsHyperbolicSpace δ (Cayley A)) (hδ0 : 0 ≤ δ) :
    ∃ kappa : ℝ, 0 ≤ kappa ∧ ∀ (y : ℕ → G) (n : ℕ),
      IsQuasiGeodesicChainAt A.carrier mu b y n →
      ∀ (f : ℝ → PointQuot A),
        IsGeodesicSegment f 0 (dist (vertexQuot A (y 0)) (vertexQuot A (y n))) →
        f 0 = vertexQuot A (y 0) →
        f (dist (vertexQuot A (y 0)) (vertexQuot A (y n))) = vertexQuot A (y n) →
        (∀ i ≤ n, ∃ t ∈ Set.Icc (0 : ℝ)
            (dist (vertexQuot A (y 0)) (vertexQuot A (y n))),
          dist (vertexQuot A (y i)) (f t) ≤ kappa) ∧
        (∀ t ∈ Set.Icc (0 : ℝ)
            (dist (vertexQuot A (y 0)) (vertexQuot A (y n))),
          ∃ i ≤ n, dist (f t) (vertexQuot A (y i)) ≤ kappa) := by
  obtain ⟨R, hR⟩ := exists_chainAt_hausdorff_bound A.carrier mu b ⌈δ⌉₊ hmu
  have hfour := isFourPointHyperbolic_of_isHyperbolicSpace_cayley A hδ
  have hreal : IsHyperbolicSpace (δ + 6) (PointQuot A) :=
    isHyperbolicSpace_pointQuot (isHyperbolicSpace_point A hδ)
  refine ⟨(R : ℝ) + 2 * (δ + 6) + 1, by positivity, ?_⟩
  intro y n hchain f hf hf0 hf1
  obtain ⟨hforward, hreverse⟩ := hR y n A.symmetricGenerating hfour hchain
  constructor
  · intro i hi
    obtain ⟨q, hq, hiq⟩ := hforward i hi
    obtain ⟨t, ht, hqt⟩ := exists_mem_geodesic_dist_le hreal hf hf0 hf1 (vertexQuot A q)
    rw [gromovProduct_vertexQuot_eq_zero_of_isBetween A hq, zero_add] at hqt
    have hiqR : dist (vertexQuot A (y i)) (vertexQuot A q) ≤ (R : ℝ) := by
      rw [dist_vertexQuot]
      exact_mod_cast hiq
    refine ⟨t, ht, ?_⟩
    linarith [dist_triangle (vertexQuot A (y i)) (vertexQuot A q) (f t)]
  · intro t ht
    obtain ⟨q, hq, htq⟩ := exists_between_vertex_near_geodesic A hreal hf hf0 hf1 ht
    obtain ⟨i, hi, hqi⟩ := hreverse q hq
    have hqiR : dist (vertexQuot A q) (vertexQuot A (y i)) ≤ (R : ℝ) := by
      rw [dist_vertexQuot]
      exact_mod_cast hqi
    refine ⟨i, hi, ?_⟩
    linarith [dist_triangle (f t) (vertexQuot A q) (vertexQuot A (y i))]

end GroupApproximation.GGT.CayleyGeodesicModel

#audit_axioms GroupApproximation.GGT.CayleyGeodesicModel.dist_vertexQuot
#audit_axioms GroupApproximation.GGT.CayleyGeodesicModel.exists_between_vertex_near_geodesic
#audit_axioms GroupApproximation.GGT.CayleyGeodesicModel.exists_chain_realization_hausdorff_bound
