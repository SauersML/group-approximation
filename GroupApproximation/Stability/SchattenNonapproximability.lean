import GroupApproximation.Algebra.VisibleQuotient
import GroupApproximation.Analysis.SingularValueOrder
import GroupApproximation.Leavitt.HilbertHotelModelNonMF
import GroupApproximation.Sofic.FiniteDimensionalResidual
import GroupApproximation.Stability.MixedApproximation
import GroupApproximation.Stability.UnnormalizedSchattenApproximation

/-!
# The exact finite-Schatten nonapproximability frontier

This file connects the literal unnormalized Schatten approximation predicate
to the repository's unconditional full-MF-radical witness.  Every Schatten
almost representation with exponent `p ≥ 1` is an operator-norm almost
representation, because the operator norm is bounded by the unnormalized
Schatten quantity.  Consequently, if the source has full norm-MF residual,
every such sequence converges to the identity in operator norm.

For a nontrivial involution this reduces nonapproximability to one
finite-dimensional statement: once a unitary `U` lies in the open
operator-norm unit ball about the identity, its Schatten displacement from
the identity is bounded by its involution defect.  The scalar version is
proved in `UnnormalizedSchattenApproximation`; the remaining matrix statement
requires matching the singular-value lists under spectral calculus.  It is
named explicitly below.  No literature theorem, construction datum, or
assumption is hidden in an endpoint.
-/

namespace GroupApproximation
namespace SchattenNonapproximability

open Filter
open scoped Matrix.Norms.L2Operator
open UnnormalizedSchattenApproximation

/-! ## Schatten control gives an operator-norm corona model -/

/-- A literal unnormalized Schatten almost representation with `p ≥ 1`
forgets to an operator-norm almost representation on the same matrix sizes. -/
noncomputable def toOpAlmostRepresentation
    {p : ℝ} {G : Type} [Group G] (A : AlmostRepresentation p G)
    (hp : 1 ≤ p) : OpAlmostRepresentation G where
  model n := naturalFiniteModel (A.dimension n).1
  modelNonempty n := by
    simpa using (A.dimension n).2
  map n g := A.map n g
  asymptoticallyMultiplicative g h ε hε := by
    obtain ⟨N, hN⟩ := A.asymptoticallyMultiplicative g h ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    exact (operatorNorm_le_schattenPNorm hp _).trans (hN n hn).le

@[simp] theorem toOpAlmostRepresentation_map
    {p : ℝ} {G : Type} [Group G] (A : AlmostRepresentation p G)
    (hp : 1 ≤ p) (n : ℕ) (g : G) :
    (toOpAlmostRepresentation A hp).map n g = A.map n g := rfl

/-- Full norm-MF residual forces every Schatten almost representation to
converge pointwise to the identity in operator norm. -/
theorem opNorm_tendsto_zero_of_normMFResidual_eq_top
    {p : ℝ} {G : Type} [Group G] [Countable G]
    (hp : 1 ≤ p) (htop : normMFResidual G = ⊤)
    (A : AlmostRepresentation p G) (g : G) :
    Tendsto
      (fun n ↦ ‖(A.map n g : Matrix (Fin (A.dimension n).1)
        (Fin (A.dimension n).1) ℂ) - 1‖)
      atTop (nhds 0) := by
  let B : OpAlmostRepresentation G := toOpAlmostRepresentation A hp
  let rho : G →* NormMatrixCoronaUnitary B.model := B.coronaHom
  have hrho : rho g = 1 :=
    map_eq_one_of_normMFResidual_eq_top_to_isOperatorMF htop
      (normMatrixCoronaUnitary_isOperatorMF B.model B.modelNonempty) rho g
  have hnull : (fun n ↦ B.map n g) ∈ nullCofiniteOpSubgroup B.model :=
    (QuotientGroup.eq_one_iff _).mp (by
      simpa [rho, OpAlmostRepresentation.coronaHom] using hrho)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have heventual := hnull ε hε
  rw [Nat.cofinite_eq_atTop] at heventual
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp heventual
  refine ⟨N, fun n hn ↦ ?_⟩
  have hsmall := hN n hn
  change ‖(A.map n g : Matrix (Fin (A.dimension n).1)
    (Fin (A.dimension n).1) ℂ) - 1‖ < ε at hsmall
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  exact hsmall

/-! ## The exact analytic boundary -/

/-- The finite-dimensional involution-defect inequality needed to turn
operator-norm collapse into unnormalized Schatten collapse.  Its scalar
counterpart is
`norm_sub_one_le_norm_sq_sub_one_of_norm_sub_one_lt_one`.

The orientation on the right is chosen to agree literally with the defect
field of `AlmostRepresentation`. -/
structure InvolutionDefectDominates (p : ℝ) : Prop where
  bound : ∀ (d : PositiveDimension) (U : UnitaryTarget d),
    ‖(U : Matrix (Fin d.1) (Fin d.1) ℂ) - 1‖ < 1 →
      schattenPDist p U 1 ≤ schattenPDist p 1 (U * U)

/-! The pointwise operator estimate behind the desired singular-value
comparison. -/

/-- If an operator is within one of the identity, multiplication by
`T + 1` cannot decrease vector norms. -/
theorem norm_le_norm_add_one_apply_of_norm_sub_one_lt_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (hT : ‖T - 1‖ < 1) (x : E) :
    ‖x‖ ≤ ‖(T + 1) x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have herror : ‖(T - 1) x‖ < ‖x‖ := by
    calc
      ‖(T - 1) x‖ ≤ ‖T - 1‖ * ‖x‖ := (T - 1).le_opNorm x
      _ < 1 * ‖x‖ := by gcongr
      _ = ‖x‖ := one_mul _
  have hsplit : (2 : ℂ) • x = (T + 1) x - (T - 1) x := by
    simp [two_smul]
  have htriangle := norm_sub_le ((T + 1) x) ((T - 1) x)
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [← hsplit, norm_smul, htwo] at htriangle
  linarith

/-- For an approximate unitary involution, the squared defect dominates the
linear defect on every vector.  The remaining passage from this pointwise
inequality to ordered singular values is the finite-dimensional min--max
principle absent from Mathlib's current singular-value API. -/
theorem pointwise_involutionDefectDominates
    (d : PositiveDimension) (U : UnitaryTarget d)
    (hU : ‖(U : Matrix (Fin d.1) (Fin d.1) ℂ) - 1‖ < 1)
    (x : EuclideanSpace ℂ (Fin d.1)) :
    ‖(Matrix.toEuclideanCLM (n := Fin d.1) (𝕜 := ℂ))
        ((U : Matrix (Fin d.1) (Fin d.1) ℂ) - 1) x‖ ≤
      ‖(Matrix.toEuclideanCLM (n := Fin d.1) (𝕜 := ℂ))
        (1 - (U : Matrix (Fin d.1) (Fin d.1) ℂ) ^ 2) x‖ := by
  let Φ := Matrix.toEuclideanCLM (n := Fin d.1) (𝕜 := ℂ)
  let T : EuclideanSpace ℂ (Fin d.1) →L[ℂ] EuclideanSpace ℂ (Fin d.1) :=
    Φ (U : Matrix (Fin d.1) (Fin d.1) ℂ)
  let y := Φ
    ((U : Matrix (Fin d.1) (Fin d.1) ℂ) - 1) x
  have hT : ‖T - 1‖ < 1 := by
    calc
      ‖T - 1‖ = ‖Φ ((U : Matrix (Fin d.1) (Fin d.1) ℂ) - 1)‖ := by
        rw [map_sub, map_one]
      _ = ‖(U : Matrix (Fin d.1) (Fin d.1) ℂ) - 1‖ :=
        Matrix.l2_opNorm_toEuclideanCLM _
      _ < 1 := hU
  have hpoint := norm_le_norm_add_one_apply_of_norm_sub_one_lt_one T hT y
  change ‖Φ ((U : Matrix (Fin d.1) (Fin d.1) ℂ) - 1) x‖ ≤ _
  calc
    ‖Φ ((U : Matrix (Fin d.1) (Fin d.1) ℂ) - 1) x‖ ≤
        ‖(Φ (U : Matrix (Fin d.1) (Fin d.1) ℂ) + 1)
          (Φ ((U : Matrix (Fin d.1) (Fin d.1) ℂ) - 1) x)‖ := hpoint
    _ = ‖Φ (((U : Matrix (Fin d.1) (Fin d.1) ℂ) + 1) *
          ((U : Matrix (Fin d.1) (Fin d.1) ℂ) - 1)) x‖ := by
      rw [← map_one Φ, ← map_add, map_mul]
      rfl
    _ = ‖Φ (-(1 - (U : Matrix (Fin d.1) (Fin d.1) ℂ) ^ 2)) x‖ := by
      congr 2
      noncomm_ring
    _ = ‖Φ (1 - (U : Matrix (Fin d.1) (Fin d.1) ℂ) ^ 2) x‖ := by
      rw [map_neg, neg_apply, norm_neg]

/-- Matrix form of the finite-dimensional involution-defect inequality. -/
theorem schattenPNorm_sub_one_le_involutionDefect
    (p : ℝ) (hp : 1 ≤ p) (d : PositiveDimension) (U : UnitaryTarget d)
    (hU : ‖(U : Matrix (Fin d.1) (Fin d.1) ℂ) - 1‖ < 1) :
    schattenPNorm p ((U : Matrix (Fin d.1) (Fin d.1) ℂ) - 1) ≤
      schattenPNorm p (1 - (U : Matrix (Fin d.1) (Fin d.1) ℂ) ^ 2) := by
  let A : Matrix (Fin d.1) (Fin d.1) ℂ :=
    (U : Matrix (Fin d.1) (Fin d.1) ℂ) - 1
  let B : Matrix (Fin d.1) (Fin d.1) ℂ :=
    1 - (U : Matrix (Fin d.1) (Fin d.1) ℂ) ^ 2
  have hpoint : ∀ x : EuclideanSpace ℂ (Fin d.1),
      ‖(Matrix.toEuclideanLin A) x‖ ≤ ‖(Matrix.toEuclideanLin B) x‖ := by
    intro x
    change
      ‖(Matrix.toEuclideanCLM (n := Fin d.1) (𝕜 := ℂ)
          ((U : Matrix (Fin d.1) (Fin d.1) ℂ) - 1)) x‖ ≤
        ‖(Matrix.toEuclideanCLM (n := Fin d.1) (𝕜 := ℂ)
          (1 - (U : Matrix (Fin d.1) (Fin d.1) ℂ) ^ 2)) x‖
    exact pointwise_involutionDefectDominates d U hU x
  change schattenPNorm p A ≤ schattenPNorm p B
  exact schattenPNorm_mono_of_singularValues_le hp fun k ↦ by
    have hfinrank :
        Module.finrank ℂ (EuclideanSpace ℂ (Fin d.1)) = d.1 := by
      simp [finrank_euclideanSpace]
    let j : Fin (Module.finrank ℂ (EuclideanSpace ℂ (Fin d.1))) :=
      Fin.cast hfinrank.symm k
    simpa [j] using
      SingularValueOrder.singularValues_le_of_norm_apply_le
        (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) hpoint j

/-- The finite-dimensional involution-defect inequality holds for every
unnormalized Schatten exponent `p ≥ 1`. -/
theorem involutionDefectDominates (p : ℝ) (hp : 1 ≤ p) :
    InvolutionDefectDominates p := by
  refine ⟨fun d U hU ↦ ?_⟩
  simpa only [schattenPDist, Submonoid.coe_one, Submonoid.coe_mul, pow_two] using
    schattenPNorm_sub_one_le_involutionDefect p hp d U hU

/-- Positive limsup separation is witnessed infinitely often above half of
that limsup. -/
theorem frequently_half_limsup_lt_schattenPDist
    {p : ℝ} {G : Type} [Group G] (A : AlmostRepresentation p G) (z : G)
    (hsep : 0 < Filter.limsup
      (fun n ↦ schattenPDist p (A.map n z) 1) Filter.atTop) :
    ∃ᶠ n in Filter.atTop,
      Filter.limsup (fun m ↦ schattenPDist p (A.map m z) 1) Filter.atTop / 2 <
        schattenPDist p (A.map n z) 1 := by
  have hcob : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
      (fun n ↦ schattenPDist p (A.map n z) 1) :=
    Filter.isCoboundedUnder_le_of_le Filter.atTop fun n ↦
      schattenPDist_nonneg p (A.map n z) 1
  exact Filter.frequently_lt_of_lt_limsup hcob (by linarith)

/-- Full norm-MF residual eventually puts the image of any fixed element in
the open operator-norm unit ball about the identity. -/
theorem eventually_opNorm_map_sub_one_lt_one
    {p : ℝ} {G : Type} [Group G] [Countable G]
    (hp : 1 ≤ p) (htop : normMFResidual G = ⊤)
    (A : AlmostRepresentation p G) (z : G) :
    ∀ᶠ n in Filter.atTop,
      ‖(A.map n z : Matrix (Fin (A.dimension n).1)
        (Fin (A.dimension n).1) ℂ) - 1‖ < 1 := by
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1
    (opNorm_tendsto_zero_of_normMFResidual_eq_top hp htop A z)) 1 zero_lt_one
  exact Filter.eventually_atTop.2 ⟨N, fun n hn ↦ by
    simpa [Real.dist_eq] using hN n hn⟩

/-- Multiplicativity at an involution makes its squared defect eventually
smaller than half of any positive limsup separation. -/
theorem eventually_involutionDefect_lt_half_limsup
    {p : ℝ} {G : Type} [Group G] (A : AlmostRepresentation p G)
    (hone : ∀ n, A.map n 1 = 1) {z : G} (hz_sq : z * z = 1)
    (hsep : 0 < Filter.limsup
      (fun n ↦ schattenPDist p (A.map n z) 1) Filter.atTop) :
    ∀ᶠ n in Filter.atTop,
      schattenPDist p 1 (A.map n z * A.map n z) <
        Filter.limsup
          (fun m ↦ schattenPDist p (A.map m z) 1) Filter.atTop / 2 := by
  obtain ⟨N, hN⟩ := A.asymptoticallyMultiplicative z z
    (Filter.limsup
      (fun n ↦ schattenPDist p (A.map n z) 1) Filter.atTop / 2) (by linarith)
  filter_upwards [eventually_ge_atTop N] with n hn
  simpa only [hz_sq, hone n] using hN n hn

theorem false_of_separated_involution_almostRepresentation
    {p : ℝ} {G : Type} [Group G] [Countable G]
    (hp : 1 ≤ p) (htop : normMFResidual G = ⊤) (A : AlmostRepresentation p G)
    (hone : ∀ n, A.map n 1 = 1) {z : G} (hz_sq : z * z = 1)
    (hL : 0 < Filter.limsup
      (fun n ↦ schattenPDist p (A.map n z) 1) Filter.atTop) : False := by
  have hfrequent : ∃ᶠ n in Filter.atTop,
      Filter.limsup
          (fun m ↦ schattenPDist p (A.map m z) 1) Filter.atTop / 2 <
        schattenPDist p (A.map n z) 1 :=
    frequently_half_limsup_lt_schattenPDist A z hL
  have hopEventually : ∀ᶠ n in Filter.atTop,
      ‖(A.map n z : Matrix (Fin (A.dimension n).1)
        (Fin (A.dimension n).1) ℂ) - 1‖ < 1 :=
    eventually_opNorm_map_sub_one_lt_one hp htop A z
  have hdefEventually : ∀ᶠ n in Filter.atTop,
      schattenPDist p 1 (A.map n z * A.map n z) <
        Filter.limsup
          (fun m ↦ schattenPDist p (A.map m z) 1) Filter.atTop / 2 :=
    eventually_involutionDefect_lt_half_limsup A hone hz_sq hL
  obtain ⟨n, hfar, hopn, hdefn⟩ :=
    (hfrequent.and_eventually (hopEventually.and hdefEventually)).exists
  exact (not_lt_of_ge
      ((involutionDefectDominates p hp).bound (A.dimension n) (A.map n z) hopn))
    (hdefn.trans hfar)

/-- A nontrivial involution in a countable full-MF-radical group rules out
unnormalized Schatten-`p` approximation for every `p ≥ 1`. -/
theorem not_isApproximated_of_normMFResidual_eq_top_of_involution
    {p : ℝ} {G : Type} [Group G] [Countable G]
    (hp : 1 ≤ p) (htop : normMFResidual G = ⊤) {z : G}
    (hz_sq : z * z = 1) (hz_ne : z ≠ 1) :
    ¬ IsApproximated p G := by
  rintro ⟨A, hone, hseparate⟩
  exact false_of_separated_involution_almostRepresentation hp htop A hone
    hz_sq (hseparate z hz_ne)

/-! ## The unconditional concrete group-theoretic witness -/

/-- The Hilbert-hotel model has no nontrivial operator-MF quotient. -/
theorem hilbertHotelModel_hasNoNontrivialOperatorMFQuotient :
    HasNoNontrivialOperatorMFQuotient HilbertHotel.Cover.Model := by
  intro H _ hH f hf
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨gx, rfl⟩ := hf x
  obtain ⟨gy, rfl⟩ := hf y
  rw [map_eq_one_of_normMFResidual_eq_top_to_isOperatorMF
      HilbertHotel.Cover.normMFResidual_model_eq_top hH f gx,
    map_eq_one_of_normMFResidual_eq_top_to_isOperatorMF
      HilbertHotel.Cover.normMFResidual_model_eq_top hH f gy]

/-- Its distinguished normally generating defect is a nontrivial
involution lying in the finite residual. -/
theorem hilbertHotelModel_involution_profile :
    HilbertHotel.Cover.defectModel ≠ 1 ∧
      HilbertHotel.Cover.defectModel * HilbertHotel.Cover.defectModel = 1 ∧
      HilbertHotel.Cover.defectModel ∈ finiteResidual HilbertHotel.Cover.Model := by
  refine ⟨HilbertHotel.Cover.defectModel_ne_one, ?_, ?_⟩
  · simpa [pow_two] using HilbertHotel.Cover.defectModel_sq
  · apply actualCoronaMFResidual_le_finiteResidual
    rw [actualCoronaMFResidual_eq_coronaMFResidual,
      coronaMFResidual_eq_normMFResidual,
      HilbertHotel.Cover.normMFResidual_model_eq_top]
    trivial

/-- The explicit Hilbert-hotel model is not approximable in any unnormalized
Schatten exponent `p ≥ 1`. -/
theorem hilbertHotelModel_not_isApproximated
    (p : ℝ) (hp : 1 ≤ p) :
    ¬ IsApproximated p HilbertHotel.Cover.Model :=
  not_isApproximated_of_normMFResidual_eq_top_of_involution hp
    HilbertHotel.Cover.normMFResidual_model_eq_top
    (by simpa [pow_two] using HilbertHotel.Cover.defectModel_sq)
    HilbertHotel.Cover.defectModel_ne_one

/-- Closed proposition recording all unconditional structure needed by the
finite-Schatten route, with no literature construction supplied to the proof. -/
def FullRadicalInvolutionWitnessExists : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Countable G) (z : G),
    Group.FG G ∧ z ≠ 1 ∧ z * z = 1 ∧ z ∈ finiteResidual G ∧
      normMFResidual G = ⊤ ∧ HasNoNontrivialOperatorMFQuotient G

theorem fullRadicalInvolutionWitnessExists :
    FullRadicalInvolutionWitnessExists := by
  refine ⟨HilbertHotel.Cover.Model, inferInstance, inferInstance,
    HilbertHotel.Cover.defectModel, HilbertHotel.Cover.model_fg,
    HilbertHotel.Cover.defectModel_ne_one, ?_, ?_,
    HilbertHotel.Cover.normMFResidual_model_eq_top,
    hilbertHotelModel_hasNoNontrivialOperatorMFQuotient⟩
  · simpa [pow_two] using HilbertHotel.Cover.defectModel_sq
  · exact hilbertHotelModel_involution_profile.2.2

#audit_axioms toOpAlmostRepresentation
#audit_axioms opNorm_tendsto_zero_of_normMFResidual_eq_top
#audit_axioms involutionDefectDominates
#audit_axioms not_isApproximated_of_normMFResidual_eq_top_of_involution
#audit_axioms hilbertHotelModel_not_isApproximated
#audit_closed_axioms fullRadicalInvolutionWitnessExists

end SchattenNonapproximability
end GroupApproximation
