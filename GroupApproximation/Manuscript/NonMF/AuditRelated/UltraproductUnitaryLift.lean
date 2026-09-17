import GroupApproximation.Analysis.FilterMatrixCStarCorona
import GroupApproximation.Analysis.NormMatrixCoronaUnitary
import GroupApproximation.Sofic.KazhdanCornerPolar
import GroupApproximation.Sofic.WeakMFUltraproduct
import GroupApproximation.Meta.AxiomGuard

/-!
# The unitary group of a norm ultraproduct of matrix algebras

`non_mf_groups_exist.tex`, Related work, lines 327--332:

> The MF problem itself was answered negatively in 2020: the failure of the
> Connes embedding problem [MIPRE] yields a II_1 factor that embeds in no
> norm ultraproduct of matrix algebras, hence a separable stably finite
> C*-algebra that is not MF [GoldbringHart, Prop 6.1, Rem 6.2].

This module supplies the analytic bridge used by the endpoint of that
sentence in `AuditRelated/ConnesEmbeddingIIOneFactor`.  The norm ultraproduct
of matrix algebras along an ultrafilter `ω` is the genuine C*-algebra
`FilterMatrixCStarCorona (fun n ↦ X n) ω`; the repository's group-level
target is `UniversalWeakMF ω X`, the unitary sequences modulo the sequences
converging to one along `ω`.  We prove that the two are the same group:

* `unitarySequenceToFilterCorona` sends a coordinatewise unitary sequence to
  its class, which is unitary;
* its kernel is exactly the `ω`-null subgroup, so it descends to an injective
  homomorphism `ultraproductToFilterCoronaUnitary`;
* it is surjective, by finite-dimensional polar correction of a representative
  (the argument of `Analysis/NormMatrixCoronaUnitary` at `cofinite`, which uses
  nothing about the filter);
* `ultraproductUnitaryEquiv` packages the isomorphism.

No hypothesis beyond the data (a sequence of finite models and an
ultrafilter) appears.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace AuditRelated

open Filter Matrix
open scoped Matrix.Norms.L2Operator ENNReal

variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ)

noncomputable section

/-- Every element of the norm ultraproduct is the class of a bounded sequence. -/
theorem ultraproductCoronaMk_surjective :
    Function.Surjective
      (filterMatrixCStarCoronaMk (fun n ↦ X n) (ω : Filter ℕ)) := by
  unfold filterMatrixCStarCoronaMk FilterMatrixCStarCorona
  exact Ideal.Quotient.mk_surjective

/-- Coordinatewise unitary sequences map to unitaries of the norm
ultraproduct. -/
def unitarySequenceToFilterCorona :
    (∀ n, Matrix.unitaryGroup (X n) ℂ) →*
      unitary (FilterMatrixCStarCorona (fun n ↦ X n) (ω : Filter ℕ)) where
  toFun u := ⟨filterMatrixCStarCoronaMk (fun n ↦ X n) (ω : Filter ℕ)
      (unitarySequenceBounded X u),
    filterMatrixCStarCoronaMk_mem_unitary (fun n ↦ X n) (ω : Filter ℕ)
      (unitarySequenceBounded X u)
      (by
        ext n i j
        exact congrArg (fun A : Matrix (X n) (X n) ℂ ↦ A i j)
          (Unitary.star_mul_self_of_mem (u n).property))
      (by
        ext n i j
        exact congrArg (fun A : Matrix (X n) (X n) ℂ ↦ A i j)
          (Unitary.mul_star_self_of_mem (u n).property))⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply Subtype.ext
    simp

/-- Exact kernel computation: a unitary sequence has trivial class precisely
when it converges to one in operator norm along `ω`. -/
theorem unitarySequenceToFilterCorona_eq_one_iff
    (u : ∀ n, Matrix.unitaryGroup (X n) ℂ) :
    unitarySequenceToFilterCorona X ω u = 1 ↔ IsNullOpSeq ω X u := by
  unfold unitarySequenceToFilterCorona
  change (⟨filterMatrixCStarCoronaMk (fun n ↦ X n) (ω : Filter ℕ)
      (unitarySequenceBounded X u), _⟩ :
      unitary (FilterMatrixCStarCorona (fun n ↦ X n) (ω : Filter ℕ))) = 1 ↔ _
  rw [Subtype.ext_iff]
  rw [← sub_eq_zero]
  change filterMatrixCStarCoronaMk (fun n ↦ X n) (ω : Filter ℕ)
    (unitarySequenceBounded X u - 1) = 0 ↔ _
  rw [filterMatrixCStarCoronaMk_eq_zero_iff]
  rw [IsNullMatrixSequence, Metric.tendsto_nhds]
  simp only [Real.dist_eq, sub_zero, abs_norm]
  rfl

theorem nullOpSubgroup_le_unitarySequenceToFilterCorona_ker :
    nullOpSubgroup ω X ≤ (unitarySequenceToFilterCorona X ω).ker := by
  intro u hu
  exact (unitarySequenceToFilterCorona_eq_one_iff X ω u).mpr hu

/-- The canonical map from the group-level operator-norm ultraproduct to the
unitary group of the C*-algebraic norm ultraproduct. -/
def ultraproductToFilterCoronaUnitary :
    UniversalWeakMF ω X →*
      unitary (FilterMatrixCStarCorona (fun n ↦ X n) (ω : Filter ℕ)) :=
  QuotientGroup.lift (nullOpSubgroup ω X)
    (unitarySequenceToFilterCorona X ω)
    (nullOpSubgroup_le_unitarySequenceToFilterCorona_ker X ω)

@[simp] theorem ultraproductToFilterCoronaUnitary_mk
    (u : ∀ n, Matrix.unitaryGroup (X n) ℂ) :
    ultraproductToFilterCoronaUnitary X ω (QuotientGroup.mk u) =
      unitarySequenceToFilterCorona X ω u :=
  QuotientGroup.lift_mk (nullOpSubgroup ω X)
    (nullOpSubgroup_le_unitarySequenceToFilterCorona_ker X ω) u

theorem ultraproductToFilterCoronaUnitary_injective :
    Function.Injective (ultraproductToFilterCoronaUnitary X ω) := by
  rw [← (ultraproductToFilterCoronaUnitary X ω).ker_eq_bot_iff]
  ext q
  induction q using Quotient.inductionOn with
  | _ u =>
    simp only [MonoidHom.mem_ker, ultraproductToFilterCoronaUnitary_mk]
    rw [unitarySequenceToFilterCorona_eq_one_iff]
    exact (@QuotientGroup.eq_one_iff _ _ (nullOpSubgroup ω X) _ u).symm

/-- Every unitary of the norm ultraproduct has a coordinatewise unitary
representative: polar-correct a representative wherever its Gram defect is at
most `1/2`, which happens `ω`-eventually. -/
theorem ultraproductToFilterCoronaUnitary_surjective :
    Function.Surjective (ultraproductToFilterCoronaUnitary X ω) := by
  rintro ⟨x, hx⟩
  obtain ⟨a, rfl⟩ := ultraproductCoronaMk_surjective X ω x
  have hgramZero :
      filterMatrixCStarCoronaMk (fun n ↦ X n) (ω : Filter ℕ)
        (star a * a - 1) = 0 := by
    rw [map_sub, map_mul, map_one, ← filterMatrixCStarCorona_star_mk]
    exact sub_eq_zero.mpr hx.1
  have hgram : IsNullMatrixSequence (fun n ↦ X n) (ω : Filter ℕ)
      (star a * a - 1) :=
    (filterMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) (ω : Filter ℕ) _).mp
      hgramZero
  have hgramTendsto :
      Tendsto (fun n ↦
        ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖) (ω : Filter ℕ)
          (nhds 0) := by
    simpa [IsNullMatrixSequence, KazhdanCornerMatrices.cornerGram,
      lp.star_apply, Matrix.star_eq_conjTranspose] using hgram
  have hgood : ∀ᶠ n in (ω : Filter ℕ),
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
  have hdiff : IsNullMatrixSequence (fun n ↦ X n) (ω : Filter ℕ)
      (unitarySequenceBounded X u - a) := by
    apply squeeze_zero'
      (Eventually.of_forall fun n ↦
        norm_nonneg ((unitarySequenceBounded X u - a) n))
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
  rw [ultraproductToFilterCoronaUnitary_mk]
  apply Subtype.ext
  change filterMatrixCStarCoronaMk (fun n ↦ X n) (ω : Filter ℕ)
      (unitarySequenceBounded X u) =
    filterMatrixCStarCoronaMk (fun n ↦ X n) (ω : Filter ℕ) a
  rw [← sub_eq_zero, ← map_sub]
  exact (filterMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ X n) (ω : Filter ℕ)
    _).mpr hdiff

/-- **The operator-norm ultraproduct group is the unitary group of the norm
ultraproduct of matrix algebras.** -/
def ultraproductUnitaryEquiv :
    UniversalWeakMF ω X ≃*
      unitary (FilterMatrixCStarCorona (fun n ↦ X n) (ω : Filter ℕ)) :=
  MulEquiv.ofBijective (ultraproductToFilterCoronaUnitary X ω)
    ⟨ultraproductToFilterCoronaUnitary_injective X ω,
      ultraproductToFilterCoronaUnitary_surjective X ω⟩

end

end AuditRelated
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.AuditRelated.unitarySequenceToFilterCorona_eq_one_iff
#audit_axioms GroupApproximation.Manuscript.NonMF.AuditRelated.ultraproductToFilterCoronaUnitary_injective
#audit_axioms GroupApproximation.Manuscript.NonMF.AuditRelated.ultraproductToFilterCoronaUnitary_surjective
#audit_axioms GroupApproximation.Manuscript.NonMF.AuditRelated.ultraproductUnitaryEquiv
