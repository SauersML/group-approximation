import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Sofic.ExteriorMFProfile
import GroupApproximation.Stability.LinearMetricApproximation
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Matrix.Normed

/-!
# Unnormalized Schatten approximation and stability

This file states the finite-Schatten approximation and stability predicates
literally.  The approximation predicate uses one sequence of maps and positive
`limsup` displacement for every nonidentity element.  All matrix dimensions
are positive.

For arbitrary real `p`, the unnormalized Schatten `p`-distance is defined from
the singular values.  The residual-finiteness implication does not require the
Schatten triangle inequality.  Indeed, the approximation maps are normalized
at the identity.  If the nearby homomorphism killed a separated element, its
distance from the approximation map at that element would therefore be exactly
the element's displacement from the identity.

At `p = 2`, the Schatten norm is the Frobenius norm.  Mathlib supplies the
Frobenius normed-group structure, so the stability-plus-approximation argument
is proved unconditionally in that case by the generic linear-metric theorem.
-/

namespace GroupApproximation
namespace UnnormalizedSchattenApproximation

open Filter
open scoped Matrix

universe u

/-- A positive finite matrix dimension. -/
abbrev PositiveDimension := {d : ℕ // 0 < d}

/-- The unitary group in a specified positive dimension. -/
abbrev UnitaryTarget (d : PositiveDimension) :=
  Matrix.unitaryGroup (Fin d.1) ℂ

/-- The unnormalized Schatten `p`-norm, defined as the `ℓᵖ`-norm of the
singular-value list.  No normalization by the matrix dimension occurs. -/
noncomputable def schattenPNorm (p : ℝ) {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  Real.rpow
    (∑ k ∈ Finset.range d,
      Real.rpow ((Matrix.toEuclideanLin A).singularValues k) p)
    (1 / p)

/-- The unnormalized Schatten `p`-distance between two unitary matrices. -/
noncomputable def schattenPDist (p : ℝ) {d : PositiveDimension}
    (U V : UnitaryTarget d) : ℝ :=
  schattenPNorm p
    ((U : Matrix (Fin d.1) (Fin d.1) ℂ) -
      (V : Matrix (Fin d.1) (Fin d.1) ℂ))

/-- The singular-value formula for the unnormalized Schatten quantity is
nonnegative for every real exponent. -/
theorem schattenPNorm_nonneg (p : ℝ) {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ schattenPNorm p A := by
  exact Real.rpow_nonneg
    (Finset.sum_nonneg fun k _ ↦
      Real.rpow_nonneg
        ((Matrix.toEuclideanLin A).singularValues_nonneg k) p)
    (1 / p)

/-- Every singular value occurring in the finite-dimensional sum is bounded
by the unnormalized Schatten `p`-quantity.  This is the scalar `ℓ^p`
estimate, proved directly from nonnegativity of the singular values. -/
theorem singularValue_le_schattenPNorm {p : ℝ} (hp : 1 ≤ p) {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) (k : Fin d) :
    (Matrix.toEuclideanLin A).singularValues k ≤ schattenPNorm p A := by
  let T := Matrix.toEuclideanLin A
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hsingular : 0 ≤ T.singularValues k := T.singularValues_nonneg k
  have hsum :
      0 ≤ ∑ j ∈ Finset.range d, Real.rpow (T.singularValues j) p :=
    Finset.sum_nonneg fun j _ ↦
      Real.rpow_nonneg (T.singularValues_nonneg j) p
  have hterm :
      Real.rpow (T.singularValues k) p ≤
        ∑ j ∈ Finset.range d, Real.rpow (T.singularValues j) p := by
    exact Finset.single_le_sum
      (fun j _ ↦ Real.rpow_nonneg (T.singularValues_nonneg j) p)
      (Finset.mem_range.mpr k.isLt)
  rw [schattenPNorm, one_div]
  exact (Real.le_rpow_inv_iff_of_pos hsingular hsum hp0).2 hterm

/-- Pointwise domination of the singular-value lists implies domination of
the corresponding unnormalized Schatten quantities. -/
theorem schattenPNorm_mono_of_singularValues_le {p : ℝ} (hp : 1 ≤ p)
    {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hAB : ∀ k : Fin d,
      (Matrix.toEuclideanLin A).singularValues k ≤
        (Matrix.toEuclideanLin B).singularValues k) :
    schattenPNorm p A ≤ schattenPNorm p B := by
  let TA := Matrix.toEuclideanLin A
  let TB := Matrix.toEuclideanLin B
  have hsumA :
      0 ≤ ∑ k ∈ Finset.range d, Real.rpow (TA.singularValues k) p :=
    Finset.sum_nonneg fun k _ ↦
      Real.rpow_nonneg (TA.singularValues_nonneg k) p
  have hsums :
      (∑ k ∈ Finset.range d, Real.rpow (TA.singularValues k) p) ≤
        ∑ k ∈ Finset.range d, Real.rpow (TB.singularValues k) p := by
    apply Finset.sum_le_sum
    intro k hk
    exact Real.rpow_le_rpow (TA.singularValues_nonneg k)
      (hAB ⟨k, Finset.mem_range.mp hk⟩) (zero_le_one.trans hp)
  unfold schattenPNorm
  exact Real.rpow_le_rpow hsumA hsums (by positivity)

section OperatorNormBounds

open scoped Matrix.Norms.L2Operator

/-- The `L²` operator norm of a nonempty square matrix is bounded by its
largest singular value. -/
theorem operatorNorm_le_largestSingularValue {d : ℕ} (hd : 0 < d)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖A‖ ≤ (Matrix.toEuclideanLin A).singularValues 0 := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let T := Matrix.toEuclideanLin A
  let D : Matrix (Fin d) (Fin d) ℂ := Aᴴ
  let H : Matrix (Fin d) (Fin d) ℂ := D * Dᴴ
  let hH : H.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self D
  obtain ⟨i, hi⟩ :=
    exists_eigenvalue_mul_conjTranspose_eq_sq_opNorm D ⟨⟨0, hd⟩⟩
  let j : Fin (Fintype.card (Fin d)) :=
    (Fintype.equivOfCardEq
      (Fintype.card_fin (Fintype.card (Fin d)))).symm i
  have hcard : 0 < Fintype.card (Fin d) := by simpa using hd
  have hfinrank :
      Module.finrank ℂ (EuclideanSpace ℂ (Fin d)) = Fintype.card (Fin d) :=
    finrank_euclideanSpace
  have hH_eq : H = Aᴴ * A := by
    simp [H, D]
  have hadjoint : T.adjoint ∘ₗ T = Matrix.toEuclideanLin H := by
    rw [hH_eq]
    simp only [T, Matrix.toEuclideanLin_eq_toLin_orthonormal]
    rw [← Matrix.toLin_conjTranspose]
    exact (Matrix.toLin_mul _ _ _ Aᴴ A).symm
  let hHlin : (Matrix.toEuclideanLin H).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have heigenvalues :
      T.isSymmetric_adjoint_comp_self.eigenvalues hfinrank =
        hHlin.eigenvalues hfinrank := by
    apply (LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff
      T.isSymmetric_adjoint_comp_self hfinrank hHlin hfinrank).2
    exact congrArg LinearMap.charpoly hadjoint
  have hj :
      T.isSymmetric_adjoint_comp_self.eigenvalues hfinrank j = ‖A‖ ^ 2 := by
    rw [heigenvalues]
    change hH.eigenvalues₀ j = ‖A‖ ^ 2
    simpa [Matrix.IsHermitian.eigenvalues, j, H, D,
      Matrix.l2_opNorm_conjTranspose] using hi
  have htop :
      ‖A‖ ^ 2 ≤
        T.isSymmetric_adjoint_comp_self.eigenvalues hfinrank
          (⟨0, hcard⟩ : Fin (Fintype.card (Fin d))) := by
    rw [← hj]
    exact T.isSymmetric_adjoint_comp_self.eigenvalues_antitone hfinrank
      (Fin.zero_le j)
  have hsquare :
      ‖A‖ ^ 2 ≤ T.singularValues 0 ^ 2 := by
    rw [T.sq_singularValues_fin hfinrank
      (⟨0, hcard⟩ : Fin (Fintype.card (Fin d)))]
    exact htop
  exact (sq_le_sq₀ (norm_nonneg A) (T.singularValues_nonneg 0)).mp hsquare

/-- The `L²` operator norm is bounded by every unnormalized Schatten
`p`-quantity with `1 ≤ p`. -/
theorem operatorNorm_le_schattenPNorm {p : ℝ} (hp : 1 ≤ p)
    {d : PositiveDimension} (A : Matrix (Fin d.1) (Fin d.1) ℂ) :
    ‖A‖ ≤ schattenPNorm p A :=
  (operatorNorm_le_largestSingularValue d.2 A).trans
    (singularValue_le_schattenPNorm hp A (⟨0, d.2⟩ : Fin d.1))

end OperatorNormBounds

/-- Scalar form of the approximate-involution estimate.  Inside the open
unit ball about `1`, multiplication by `z + 1` cannot decrease the distance
from zero, and `(z - 1)(z + 1) = z² - 1`. -/
theorem norm_sub_one_le_norm_sq_sub_one_of_norm_sub_one_lt_one
    (z : ℂ) (hz : ‖z - 1‖ < 1) :
    ‖z - 1‖ ≤ ‖z ^ 2 - 1‖ := by
  have hplus : 1 < ‖z + 1‖ := by
    have htriangle := norm_sub_le (z + 1) (z - 1)
    have hdifference : (z + 1) - (z - 1) = (2 : ℂ) := by ring
    have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [hdifference, htwo] at htriangle
    linarith
  calc
    ‖z - 1‖ ≤ ‖z - 1‖ * ‖z + 1‖ :=
      le_mul_of_one_le_right (norm_nonneg _) hplus.le
    _ = ‖(z - 1) * (z + 1)‖ := (norm_mul _ _).symm
    _ = ‖z ^ 2 - 1‖ := by
      congr 1
      ring

/-- Raising the scalar approximate-involution estimate to any nonnegative
real power preserves it. -/
theorem norm_sub_one_rpow_le_norm_sq_sub_one_rpow
    {p : ℝ} (hp : 0 ≤ p) (z : ℂ) (hz : ‖z - 1‖ < 1) :
    Real.rpow ‖z - 1‖ p ≤ Real.rpow ‖z ^ 2 - 1‖ p :=
  Real.rpow_le_rpow (norm_nonneg _)
    (norm_sub_one_le_norm_sq_sub_one_of_norm_sub_one_lt_one z hz) hp

/-- Unnormalized Schatten displacement is nonnegative. -/
theorem schattenPDist_nonneg (p : ℝ) {d : PositiveDimension}
    (U V : UnitaryTarget d) : 0 ≤ schattenPDist p U V :=
  schattenPNorm_nonneg p _

/-- A single sequence of maps into positive-dimensional unitary groups whose
multiplicative defects vanish in unnormalized Schatten `p`-distance. -/
structure AlmostRepresentation (p : ℝ) (G : Type u) [Group G] where
  dimension : ℕ → PositiveDimension
  map : ∀ n, G → UnitaryTarget (dimension n)
  asymptoticallyMultiplicative :
    ∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      schattenPDist p (map n (g * h)) (map n g * map n h) < ε

/-- Literal one-sequence approximation in unnormalized Schatten `p`-distance.
Every map sends the identity to the identity, and every nonidentity element
has positive `limsup` displacement from the target identity. -/
def IsApproximated (p : ℝ) (G : Type u) [Group G] : Prop :=
  ∃ A : AlmostRepresentation p G,
    (∀ n, A.map n 1 = 1) ∧
      ∀ g : G, g ≠ 1 →
        0 < Filter.limsup
          (fun n ↦ schattenPDist p (A.map n g) 1) Filter.atTop

/-- Unnormalized Schatten approximation passes to an embedded subgroup.
This is the subgroup step used when one places several nonapproximable groups
inside a common host: approximation of the host would restrict to an
approximation of each embedded group. -/
theorem isApproximated_of_injective
    {p : ℝ} {H G : Type u} [Group H] [Group G]
    (i : H →* G) (hi : Function.Injective i)
    (hG : IsApproximated p G) : IsApproximated p H := by
  obtain ⟨A, hone, hseparate⟩ := hG
  let B : AlmostRepresentation p H :=
    { dimension := A.dimension
      map := fun n h ↦ A.map n (i h)
      asymptoticallyMultiplicative := by
        intro g h ε hε
        simpa only [map_mul] using
          A.asymptoticallyMultiplicative (i g) (i h) ε hε }
  refine ⟨B, ?_, ?_⟩
  · intro n
    change A.map n (i 1) = 1
    rw [map_one, hone n]
  · intro h hh
    have hih : i h ≠ 1 := by
      intro hione
      apply hh
      apply hi
      simpa using hione
    change 0 < Filter.limsup
      (fun n ↦ schattenPDist p (A.map n (i h)) 1) Filter.atTop
    exact hseparate (i h) hih

/-- If an embedded subgroup is not Schatten-`p` approximated, neither is its
ambient group. -/
theorem not_isApproximated_of_injective
    {p : ℝ} {H G : Type u} [Group H] [Group G]
    (i : H →* G) (hi : Function.Injective i)
    (hH : ¬ IsApproximated p H) : ¬ IsApproximated p G :=
  fun hG ↦ hH (isApproximated_of_injective i hi hG)

/-- Literal pointwise stability in unnormalized Schatten `p`-distance. -/
def IsStable (p : ℝ) (G : Type u) [Group G] : Prop :=
  ∀ A : AlmostRepresentation p G,
    ∃ π : ∀ n, G →* UnitaryTarget (A.dimension n),
      ∀ g : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
        schattenPDist p (A.map n g) (π n g) < ε

/-- The precise general finite-Schatten residual-finiteness implication. -/
def StabilityForcesResidualFiniteness (p : ℝ) : Prop :=
  1 ≤ p → ∀ (G : Type u) [Group G] [Group.FG G],
    IsApproximated p G → IsStable p G → Group.ResiduallyFinite G

/-- Approximation and stability in the literal unnormalized Schatten
`p`-quantity force residual finiteness.  The proof is valid for every real
`p`; the hypothesis `1 ≤ p` in `StabilityForcesResidualFiniteness` only records
the finite-Schatten range of the printed statement.

No triangle inequality is used.  Positive `limsup` separation supplies a
subsequence on which a fixed nonidentity element stays away from the identity.
Stability supplies nearby homomorphisms.  Since a homomorphism sends the
identity to the identity, any one of those homomorphisms which killed the
element would make its approximation error equal to the separated
displacement.  The resulting detecting linear representation is converted to
a finite quotient by the formalized Mal'cev theorem. -/
theorem residuallyFinite_of_approximated_of_stable
    {p : ℝ} {G : Type u} [Group G] [Group.FG G]
    (happrox : IsApproximated p G) (hstable : IsStable p G) :
    Group.ResiduallyFinite G := by
  classical
  obtain ⟨A, _hone, hseparate⟩ := happrox
  obtain ⟨π, hπ⟩ := hstable A
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro x hx
  let L := Filter.limsup
    (fun n ↦ schattenPDist p (A.map n x) 1) Filter.atTop
  have hL : 0 < L := hseparate x hx
  have hcob : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
      (fun n ↦ schattenPDist p (A.map n x) 1) :=
    Filter.isCoboundedUnder_le_of_le Filter.atTop fun n ↦
      schattenPDist_nonneg p (A.map n x) 1
  have hfrequent : ∃ᶠ n in Filter.atTop,
      L / 2 < schattenPDist p (A.map n x) 1 :=
    Filter.frequently_lt_of_lt_limsup hcob (by linarith)
  obtain ⟨r, hr, hgap⟩ := Filter.extraction_of_frequently_atTop hfrequent
  obtain ⟨N, hN⟩ := hπ x (L / 2) (by linarith)
  have hclose :
      schattenPDist p (A.map (r N) x) (π (r N) x) < L / 2 :=
    hN (r N) (hr.id_le N)
  have hπx : π (r N) x ≠ 1 := by
    intro heq
    have hsmall : schattenPDist p (A.map (r N) x) 1 < L / 2 := by
      simpa [heq] using hclose
    exact (not_lt_of_ge (hgap N).le) hsmall
  let ρ : G →* Matrix.GeneralLinearGroup (Fin (A.dimension (r N)).1) ℂ :=
    Unitary.toUnits.comp (π (r N))
  have hρx : ρ x ≠ 1 := by
    intro h
    apply hπx
    apply Unitary.toUnits_injective
    simpa [ρ] using h
  haveI : Group.ResiduallyFinite ρ.range :=
    MalcevLinear.residuallyFinite_of_fg ρ.range
      (LinearMetricApproximation.range_fg ρ)
  let y : ρ.range := ρ.rangeRestrict x
  have hy : y ≠ 1 := by
    intro h
    apply hρx
    exact Subtype.ext_iff.mp h
  obtain ⟨N', hN'⟩ := Group.exists_finiteIndexNormalSubgroup_notMem y hy
  letI := N'.isNormal'
  letI := N'.isFiniteIndex'
  refine ⟨ρ.range ⧸ N'.toSubgroup, inferInstance, inferInstance,
    (QuotientGroup.mk' N'.toSubgroup).comp ρ.rangeRestrict, ?_⟩
  intro h
  apply hN'
  exact (QuotientGroup.eq_one_iff y).mp (by simpa [y] using h)

/-- The unconditional all-finite-`p` stability principle. -/
theorem stabilityForcesResidualFiniteness (p : ℝ) :
    StabilityForcesResidualFiniteness.{u} p := by
  intro _hp G _ _ happrox hstable
  exact residuallyFinite_of_approximated_of_stable happrox hstable

/-- Closed proposition expressing the stability implication simultaneously
for every finite Schatten parameter. -/
def AllFinitePStabilityForcesResidualFiniteness : Prop :=
  ∀ p : ℝ, StabilityForcesResidualFiniteness.{u} p

theorem allFinitePStabilityForcesResidualFiniteness :
    AllFinitePStabilityForcesResidualFiniteness.{u} := by
  exact stabilityForcesResidualFiniteness

/-! ## The unconditional `p = 2` specialization -/

/-- The unnormalized Schatten `2`-distance, written in its Frobenius
coordinate formula. -/
noncomputable def schattenTwoDist {d : PositiveDimension}
    (U V : UnitaryTarget d) : ℝ :=
  Real.rpow
    (∑ i : Fin d.1, ∑ j : Fin d.1,
      ‖(U : Matrix (Fin d.1) (Fin d.1) ℂ) i j - V i j‖ ^ (2 : ℝ))
    (1 / 2 : ℝ)

/-- The metric on a finite unitary group induced by the unnormalized
Frobenius norm on matrices. -/
@[reducible] noncomputable def schattenTwoMetricSpace (d : PositiveDimension) :
    MetricSpace (UnitaryTarget d) := by
  letI : NormedAddCommGroup (Matrix (Fin d.1) (Fin d.1) ℂ) :=
    Matrix.frobeniusNormedAddCommGroup
  exact MetricSpace.induced
    (fun U : UnitaryTarget d ↦ (U : Matrix (Fin d.1) (Fin d.1) ℂ))
    Subtype.coe_injective inferInstance

/-- The induced metric is exactly the displayed unnormalized Schatten
`2`-distance. -/
theorem dist_eq_schattenTwoDist (d : PositiveDimension) (U V : UnitaryTarget d) :
    @dist (UnitaryTarget d) (schattenTwoMetricSpace d).toDist U V =
      schattenTwoDist U V := by
  letI : NormedAddCommGroup (Matrix (Fin d.1) (Fin d.1) ℂ) :=
    Matrix.frobeniusNormedAddCommGroup
  change dist
    (U : Matrix (Fin d.1) (Fin d.1) ℂ)
    (V : Matrix (Fin d.1) (Fin d.1) ℂ) = _
  rw [dist_eq_norm, Matrix.frobenius_norm_def]
  rfl

/-- One-sequence approximation by positive-dimensional unitary groups in the
unnormalized Schatten `2` metric. -/
noncomputable def IsSchattenTwoApproximated (G : Type u) [Group G] : Prop := by
  letI : ∀ d : PositiveDimension, PseudoMetricSpace ↑(UnitaryTarget d) :=
    fun d ↦ (schattenTwoMetricSpace d).toPseudoMetricSpace
  exact LinearMetricApproximation.IsLimsupApproximatedBy
    (I := PositiveDimension) (M := fun d ↦ ↑(UnitaryTarget d)) G

/-- Pointwise stability for the same unnormalized Schatten `2` models. -/
noncomputable def IsSchattenTwoStable (G : Type u) [Group G] : Prop := by
  letI : ∀ d : PositiveDimension, PseudoMetricSpace ↑(UnitaryTarget d) :=
    fun d ↦ (schattenTwoMetricSpace d).toPseudoMetricSpace
  exact LinearMetricApproximation.IsStableWithRespectTo
    (I := PositiveDimension) (M := fun d ↦ ↑(UnitaryTarget d)) G

/-- The closed, unconditional Schatten-`2` stability principle.  The
approximation and stability clauses occur inside the proposition; no group or
literature theorem is supplied as construction data to its proof. -/
def SchattenTwoStabilityPrinciple : Prop :=
  ∀ (G : Type u) [Group G] [Group.FG G],
    IsSchattenTwoApproximated G → IsSchattenTwoStable G →
      Group.ResiduallyFinite G

theorem schattenTwoStabilityPrinciple : SchattenTwoStabilityPrinciple := by
  intro G _ _ happrox hstable
  letI : ∀ d : PositiveDimension, PseudoMetricSpace ↑(UnitaryTarget d) :=
    fun d ↦ (schattenTwoMetricSpace d).toPseudoMetricSpace
  apply LinearMetricApproximation.residuallyFinite_of_limsupApproximated_of_stable
    (I := PositiveDimension) (M := fun d ↦ ↑(UnitaryTarget d))
    (F := fun _ ↦ ℂ) (d := fun d ↦ d.1)
    (linear := fun _ ↦ Unitary.toUnits)
    (linear_injective := fun _ ↦ Unitary.toUnits_injective)
  · simpa [IsSchattenTwoApproximated] using happrox
  · simpa [IsSchattenTwoStable] using hstable

#audit_axioms operatorNorm_le_schattenPNorm
#audit_axioms dist_eq_schattenTwoDist
#audit_closed_axioms allFinitePStabilityForcesResidualFiniteness
#audit_closed_axioms schattenTwoStabilityPrinciple

end UnnormalizedSchattenApproximation
end GroupApproximation
