import GroupApproximation.Analysis.ShulmanCoronaHalmosCommutator
import GroupApproximation.Meta.AxiomGuard

/-!
# The asymptotically central Halmos-unitary sequence
-/

namespace GroupApproximation
namespace ShulmanCoronaHalmosCommutator

open Filter PolarLiftingGeneralCStar

noncomputable section

universe u

variable (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]
  [∀ n, Nontrivial (A n)] (l : Filter ℕ)

noncomputable local instance sequenceCoordinatePartialOrder (n : ℕ) :
    PartialOrder (A n) := CStarAlgebra.spectralOrder (A n)

noncomputable local instance sequenceCoordinateStarOrderedRing (n : ℕ) :
    StarOrderedRing (A n) := CStarAlgebra.spectralOrderedRing (A n)

abbrev Mat₂Family := fun n ↦ ShulmanHalmosDilation.Mat₂ (A n)

/-- Coordinatewise Halmos dilation, as a bounded product sequence. -/
def halmosSequence (x : BoundedCStarSequence A) (hx : ∀ n, ‖x n‖ ≤ 1) :
    BoundedCStarSequence (Mat₂Family A) :=
  ⟨fun n ↦ ShulmanHalmosDilation.halmos (x n), memℓp_infty ⟨1, by
    rintro _ ⟨n, rfl⟩
    exact le_of_eq (CStarRing.norm_of_mem_unitary
      (ShulmanHalmosDilation.halmos_mem_unitary (hx n)))⟩⟩

/-- Coordinatewise repeated diagonal placement, as a bounded product
sequence. -/
def repeatedDiagonalSequence (b : BoundedCStarSequence A) :
    BoundedCStarSequence (Mat₂Family A) :=
  ⟨fun n ↦ ShulmanHalmosDilation.diag₂ (b n) (b n),
    memℓp_infty ⟨2 * ‖b‖, by
      rintro _ ⟨n, rfl⟩
      refine (ShulmanHalmosDilation.norm_mat₂_le_sum_entries _).trans ?_
      simp only [Fin.sum_univ_two, ShulmanHalmosDilation.diag₂]
      simp
      nlinarith [boundedCStarSequence_coord_norm_le A b n,
        norm_nonneg (b n), norm_nonneg b]⟩⟩

@[simp] theorem halmosSequence_apply
    (x : BoundedCStarSequence A) (hx : ∀ n, ‖x n‖ ≤ 1) (n : ℕ) :
    halmosSequence A x hx n = ShulmanHalmosDilation.halmos (x n) :=
  rfl

/-- Every coordinate of the Halmos sequence is unitary. -/
theorem halmosSequence_mem_unitary
    (x : BoundedCStarSequence A) (hx : ∀ n, ‖x n‖ ≤ 1) (n : ℕ) :
    halmosSequence A x hx n ∈ unitary (Mat₂Family A n) :=
  ShulmanHalmosDilation.halmos_mem_unitary (hx n)

omit [∀ n, Nontrivial (A n)] in
@[simp] theorem repeatedDiagonalSequence_apply
    (b : BoundedCStarSequence A) (n : ℕ) :
    repeatedDiagonalSequence A b n = ShulmanHalmosDilation.diag₂ (b n) (b n) :=
  rfl

/-- The Halmos unitary sequence asymptotically commutes with the repeated
diagonal sequence whenever `x`, `x*`, and the two defect roots do. -/
theorem isNull_halmosSequence_commutator
    (x b : BoundedCStarSequence A) (hx : ∀ n, ‖x n‖ ≤ 1)
    (hxComm : IsNullCStarSequence A l (x * b - b * x))
    (hxStarComm : IsNullCStarSequence A l (star x * b - b * star x)) :
    IsNullCStarSequence (Mat₂Family A) l
      (halmosSequence A x hx * repeatedDiagonalSequence A b -
        repeatedDiagonalSequence A b * halmosSequence A x hx) := by
  have hleft := isNull_commutator_leftDefectRoot A l x b hx hxComm hxStarComm
  have hright := isNull_commutator_rightDefectRoot A l x b hx hxComm hxStarComm
  have hstarNeg : IsNullCStarSequence A l
      ((-star x) * b - b * (-star x)) := by
    have hident : (-star x) * b - b * (-star x) =
        -(star x * b - b * star x) := by noncomm_ring
    rw [hident]
    exact (nullCStarSequenceIdeal A l).neg_mem hxStarComm
  apply squeeze_zero'
    (Eventually.of_forall fun n ↦ norm_nonneg
      ((halmosSequence A x hx * repeatedDiagonalSequence A b -
        repeatedDiagonalSequence A b * halmosSequence A x hx) n))
  · filter_upwards with n
    simpa only [halmosSequence_apply, repeatedDiagonalSequence_apply,
      lp.infty_coeFn_mul, Pi.mul_apply, lp.coeFn_sub, Pi.sub_apply,
      lp.star_apply] using
        (ShulmanHalmosDilation.norm_halmos_commutator_diag₂_le (x n) (b n))
  · simpa only [add_zero, lp.infty_coeFn_mul, Pi.mul_apply, lp.coeFn_sub,
      Pi.sub_apply, lp.star_apply, lp.coeFn_neg, Pi.neg_apply,
      ShulmanCoronaSquareRoot.sqrtSequence_apply, leftArgument_apply,
      rightArgument_apply, ShulmanHalmosDilation.leftDefect,
      ShulmanHalmosDilation.rightDefect] using
      Filter.Tendsto.add
        (Filter.Tendsto.add (Filter.Tendsto.add hxComm hleft) hright) hstarNeg

/-! ## Closed endpoint -/

/-- Closed form of the sequence-level Halmos correction used in the
Shulman/HNN argument.  A bounded sequence of contractions whose values and
adjoints asymptotically commute with `b` has a coordinatewise unitary Halmos
dilation, and that dilation asymptotically commutes with the repeated block
diagonal of `b`. -/
def CoronaHalmosSequenceControl : Prop :=
  ∀ (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]
      [∀ n, Nontrivial (A n)] (l : Filter ℕ)
      (x b : BoundedCStarSequence A) (hx : ∀ n, ‖x n‖ ≤ 1),
    IsNullCStarSequence A l (x * b - b * x) →
    IsNullCStarSequence A l (star x * b - b * star x) →
    (∀ n, halmosSequence A x hx n ∈ unitary (Mat₂Family A n)) ∧
      IsNullCStarSequence (Mat₂Family A) l
        (halmosSequence A x hx * repeatedDiagonalSequence A b -
          repeatedDiagonalSequence A b * halmosSequence A x hx)

theorem coronaHalmosSequenceControl : CoronaHalmosSequenceControl := by
  intro A _ _ l x b hx hxComm hxStarComm
  exact ⟨halmosSequence_mem_unitary A x hx,
    isNull_halmosSequence_commutator A l x b hx hxComm hxStarComm⟩

end

end ShulmanCoronaHalmosCommutator
end GroupApproximation

#audit_closed_axioms GroupApproximation.ShulmanCoronaHalmosCommutator.coronaHalmosSequenceControl
