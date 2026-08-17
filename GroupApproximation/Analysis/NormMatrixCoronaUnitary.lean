import GroupApproximation.Analysis.NormMatrixCorona
import GroupApproximation.Sofic.KazhdanCornerPolar
import GroupApproximation.Sofic.OperatorMF

/-!
# Unitary sequences inside the norm-matrix C-star corona

This file constructs the canonical homomorphism from the cofinite quotient of
unitary matrix sequences to the unitary group of the actual C-star corona.
Its kernel computation is literal: a unitary sequence maps to one precisely
when its operator-norm distance from one tends to zero.

Every unitary in the quotient has a coordinatewise-unitary representative
modulo a null sequence: apply finite-dimensional polar correction wherever
the representative's Gram defect is at most `1/2`, and use the identity in
the finitely many remaining coordinates.  Thus the sequence quotient is
canonically isomorphic to the unitary group of the C-star corona.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator ENNReal

variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]

noncomputable section

/-- A sequence of unitary matrices is uniformly bounded, hence defines an
element of the bounded-sequence numerator. -/
def unitarySequenceBounded
    (u : ∀ n, Matrix.unitaryGroup (X n) ℂ) :
    BoundedMatrixSequence (fun n ↦ X n) :=
  ⟨fun n ↦ u n, memℓp_infty ⟨1, by
    rintro _ ⟨n, rfl⟩
    exact (CStarRing.norm_of_mem_unitary (u n).property).le⟩⟩

@[simp] theorem unitarySequenceBounded_apply
    (u : ∀ n, Matrix.unitaryGroup (X n) ℂ) (n : ℕ) :
    unitarySequenceBounded X u n = u n :=
  rfl

@[simp] theorem unitarySequenceBounded_one :
    unitarySequenceBounded X 1 = 1 := by
  ext n i j
  rfl

@[simp] theorem unitarySequenceBounded_mul
    (u v : ∀ n, Matrix.unitaryGroup (X n) ℂ) :
    unitarySequenceBounded X (u * v) =
      unitarySequenceBounded X u * unitarySequenceBounded X v := by
  ext n i j
  rfl

/-- Coordinatewise unitary sequences map to unitaries in the genuine C-star
corona. -/
def unitarySequenceToCorona :
    (∀ n, Matrix.unitaryGroup (X n) ℂ) →*
      unitary (NormMatrixCStarCorona (fun n ↦ X n)) where
  toFun u := ⟨normMatrixCStarCoronaMk (fun n ↦ X n) (unitarySequenceBounded X u), by
    constructor
    · have hmul : star (unitarySequenceBounded X u) *
          unitarySequenceBounded X u = 1 := by
        ext n i j
        exact congrArg (fun A : Matrix (X n) (X n) ℂ ↦ A i j)
          (Unitary.star_mul_self_of_mem (u n).property)
      have hstar := normMatrixCStarCorona_star_mk
        (fun n ↦ (X n : Type)) (unitarySequenceBounded X u)
      conv_lhs =>
        lhs
        rw [hstar]
      simpa only [map_mul, map_one] using
        congrArg (normMatrixCStarCoronaMk (fun n ↦ X n)) hmul
    · have hmul : unitarySequenceBounded X u *
          star (unitarySequenceBounded X u) = 1 := by
        ext n i j
        exact congrArg (fun A : Matrix (X n) (X n) ℂ ↦ A i j)
          (Unitary.mul_star_self_of_mem (u n).property)
      have hstar := normMatrixCStarCorona_star_mk
        (fun n ↦ (X n : Type)) (unitarySequenceBounded X u)
      conv_lhs =>
        rhs
        rw [hstar]
      simpa only [map_mul, map_one] using
        congrArg (normMatrixCStarCoronaMk (fun n ↦ X n)) hmul⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply Subtype.ext
    simp

/-- Exact kernel computation for the coordinatewise-unitary map. -/
theorem unitarySequenceToCorona_eq_one_iff
    (u : ∀ n, Matrix.unitaryGroup (X n) ℂ) :
    unitarySequenceToCorona X u = 1 ↔ IsNullCofiniteOpSeq X u := by
  unfold unitarySequenceToCorona
  change (⟨normMatrixCStarCoronaMk (fun n ↦ X n) (unitarySequenceBounded X u), _⟩ :
      unitary (NormMatrixCStarCorona (fun n ↦ X n))) = 1 ↔ _
  rw [Subtype.ext_iff]
  rw [← sub_eq_zero]
  change normMatrixCStarCoronaMk (fun n ↦ X n) (unitarySequenceBounded X u - 1) = 0 ↔ _
  rw [normMatrixCStarCoronaMk_eq_zero_iff]
  rw [IsNullMatrixSequence, Metric.tendsto_nhds]
  simp only [Real.dist_eq, sub_zero, abs_norm]
  rfl

theorem nullCofiniteOpSubgroup_le_unitarySequenceToCorona_ker :
    nullCofiniteOpSubgroup X ≤ (unitarySequenceToCorona X).ker := by
  intro u hu
  exact (unitarySequenceToCorona_eq_one_iff X u).mpr hu

/-- The canonical map from the unitary-sequence corona into the unitary group
of the genuine C-star corona. -/
def unitaryCoronaToCStarCoronaUnitary :
    NormMatrixCoronaUnitary X →*
      unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
  QuotientGroup.lift (nullCofiniteOpSubgroup X)
    (unitarySequenceToCorona X)
    (nullCofiniteOpSubgroup_le_unitarySequenceToCorona_ker X)

@[simp] theorem unitaryCoronaToCStarCoronaUnitary_mk
    (u : ∀ n, Matrix.unitaryGroup (X n) ℂ) :
    unitaryCoronaToCStarCoronaUnitary X (QuotientGroup.mk u) =
      unitarySequenceToCorona X u :=
  QuotientGroup.lift_mk (nullCofiniteOpSubgroup X)
    (nullCofiniteOpSubgroup_le_unitarySequenceToCorona_ker X) u

/-- No information is lost when passing from the unitary-sequence corona to
the unitary group of the C-star corona. -/
theorem unitaryCoronaToCStarCoronaUnitary_injective :
    Function.Injective (unitaryCoronaToCStarCoronaUnitary X) := by
  rw [← (unitaryCoronaToCStarCoronaUnitary X).ker_eq_bot_iff]
  ext q
  induction q using Quotient.inductionOn with
  | _ u =>
    simp only [MonoidHom.mem_ker, unitaryCoronaToCStarCoronaUnitary_mk]
    rw [unitarySequenceToCorona_eq_one_iff]
    exact (@QuotientGroup.eq_one_iff _ _ (nullCofiniteOpSubgroup X) _ u).symm

/-- Every unitary of the norm-matrix C-star corona is represented, modulo a
null sequence, by a coordinatewise unitary sequence. -/
theorem unitaryCoronaToCStarCoronaUnitary_surjective :
    Function.Surjective (unitaryCoronaToCStarCoronaUnitary X) := by
  rintro ⟨x, hx⟩
  obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ X n) x
  have hgramZero :
      normMatrixCStarCoronaMk (fun n ↦ X n) (star a * a - 1) = 0 := by
    rw [map_sub, map_mul, map_one]
    exact sub_eq_zero.mpr hx.1
  have hgram : IsNullMatrixSequence (fun n ↦ X n) cofinite (star a * a - 1) :=
    (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) _).mp hgramZero
  have hgramTendsto :
      Tendsto (fun n ↦
        ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖) cofinite (nhds 0) := by
    simpa [IsNullMatrixSequence, KazhdanCornerMatrices.cornerGram,
      lp.star_apply, Matrix.star_eq_conjTranspose] using hgram
  have hgood : ∀ᶠ n in cofinite,
      ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ) := by
    have hnear := (Metric.tendsto_nhds.mp hgramTendsto)
      (1 / 2 : ℝ) (by norm_num)
    filter_upwards [hnear] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le
  let u : ∀ n, Matrix.unitaryGroup (X n) ℂ := fun n ↦
    if hn : ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ) then
      KazhdanCornerMatrices.polarCorrectUnitary (a n)
        (KazhdanCornerMatrices.cornerGram_isHermitian (a n)) hn le_rfl
    else 1
  have hdiff : IsNullMatrixSequence (fun n ↦ X n) cofinite
      (unitarySequenceBounded X u - a) := by
    apply squeeze_zero'
      (Eventually.of_forall fun n ↦ norm_nonneg ((unitarySequenceBounded X u - a) n))
    · filter_upwards [hgood] with n hn
      change ‖(u n : Matrix (X n) (X n) ℂ) - a n‖ ≤
        ‖a‖ * (2 * ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖)
      rw [show u n = KazhdanCornerMatrices.polarCorrectUnitary (a n)
          (KazhdanCornerMatrices.cornerGram_isHermitian (a n)) hn le_rfl by
        rw [show u n = dite
            (‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ))
            (fun hn ↦ KazhdanCornerMatrices.polarCorrectUnitary (a n)
              (KazhdanCornerMatrices.cornerGram_isHermitian (a n)) hn le_rfl)
            (fun _ ↦ 1) by rfl, dif_pos hn]]
      exact (KazhdanCornerMatrices.norm_polarCorrect_sub_le_mul (a n)
        (KazhdanCornerMatrices.cornerGram_isHermitian (a n))
        (norm_nonneg _) hn le_rfl).trans
          (mul_le_mul_of_nonneg_right
            ((lp.isLUB_norm a).1 ⟨n, rfl⟩) (by positivity))
    · simpa only [mul_zero] using
        (hgramTendsto.const_mul 2).const_mul ‖a‖
  refine ⟨QuotientGroup.mk u, ?_⟩
  rw [unitaryCoronaToCStarCoronaUnitary_mk]
  apply Subtype.ext
  change normMatrixCStarCoronaMk (fun n ↦ X n) (unitarySequenceBounded X u) =
    normMatrixCStarCoronaMk (fun n ↦ X n) a
  rw [← sub_eq_zero, ← map_sub]
  exact (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) _).mpr hdiff

/-- The canonical multiplicative equivalence between the unitary-sequence
corona and the unitary group of the genuine C-star corona. -/
noncomputable def normMatrixCoronaUnitaryEquiv :
    NormMatrixCoronaUnitary X ≃*
      unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
  MulEquiv.ofBijective (unitaryCoronaToCStarCoronaUnitary X)
    ⟨unitaryCoronaToCStarCoronaUnitary_injective X,
      unitaryCoronaToCStarCoronaUnitary_surjective X⟩

end

end GroupApproximation
