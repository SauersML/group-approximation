import GroupApproximation.Analysis.NormCoronaAsymptoticLift
import GroupApproximation.Sofic.MFTraceCoronaBridge

/-!
# From an asymptotic model to an MF embedding

The coordinate maps in `NormCoronaAsymptoticLift.Model` need not preserve any
algebraic operation at a finite stage.  Their defects tend to zero in operator
norm, however, so the bounded coordinate sequences define an exact nonunital
star homomorphism into the norm-matrix corona.  If the model also recovers the
norm of every source element as a limsup, that homomorphism is faithful.

This is the reverse conversion used in the asymptotic-lifting formulation of
the MF property.  It is independent of any amalgamated-free-product
permanence theorem.
-/

namespace GroupApproximation
namespace AsymptoticModelMFEmbedding

open Filter
open scoped Matrix.Norms.L2Operator ENNReal

noncomputable section

universe u

variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- The bounded matrix sequence attached to one element of an asymptotic
model. -/
def seq (M : NormCoronaAsymptoticLift.Model (X := X) A) (a : A) :
    BoundedMatrixSequence (fun n ↦ X n) :=
  ⟨fun n ↦ M.map n a, by
    have hmem : Memℓp (fun n ↦ M.map n a) ∞ := by
      rw [memℓp_infty_iff]
      obtain ⟨C, hC⟩ := M.bounded a
      refine ⟨C, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact hC n
    exact hmem⟩

omit [∀ n, Nonempty (X n)] in
@[simp] theorem seq_apply
    (M : NormCoronaAsymptoticLift.Model (X := X) A) (a : A) (n : ℕ) :
    seq M a n = M.map n a :=
  rfl

omit [∀ n, Nonempty (X n)] in
/-- The additive-zero defect follows from complex homogeneity at scalar
zero. -/
theorem tendsto_zero
    (M : NormCoronaAsymptoticLift.Model (X := X) A) :
    Tendsto (fun n ↦ ‖M.map n 0‖) atTop (nhds 0) := by
  simpa using M.tendsto_smul (0 : ℂ) (0 : A)

/-- An asymptotic star homomorphism becomes exact after quotienting by
operator-norm-null sequences. -/
def coronaHom (M : NormCoronaAsymptoticLift.Model (X := X) A) :
    A →⋆ₙₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n) where
  toFun a := normMatrixCStarCoronaMk (fun n ↦ X n) (seq M a)
  map_smul' c a := by
    have h : normMatrixCStarCoronaMk (fun n ↦ X n) (seq M (c • a)) =
        normMatrixCStarCoronaMk (fun n ↦ X n) (c • seq M a) :=
      ShulmanTrace.coronaQuotient_eq_of_tendsto_zero (fun n ↦ X n) _ _ (by
        simpa only [seq_apply, lp.coeFn_smul, Pi.smul_apply] using
          M.tendsto_smul c a)
    rw [h, MFAlgebraDimension.normMatrixCStarCoronaMk_smul]
    rfl
  map_zero' := by
    have h : normMatrixCStarCoronaMk (fun n ↦ X n) (seq M 0) =
        normMatrixCStarCoronaMk (fun n ↦ X n) 0 :=
      ShulmanTrace.coronaQuotient_eq_of_tendsto_zero (fun n ↦ X n) _ _ (by
        simpa only [seq_apply, lp.coeFn_zero, Pi.zero_apply, sub_zero] using
          tendsto_zero M)
    rw [h, map_zero]
  map_add' a b := by
    have h : normMatrixCStarCoronaMk (fun n ↦ X n) (seq M (a + b)) =
        normMatrixCStarCoronaMk (fun n ↦ X n) (seq M a + seq M b) :=
      ShulmanTrace.coronaQuotient_eq_of_tendsto_zero (fun n ↦ X n) _ _ (by
        simpa only [seq_apply, lp.coeFn_add, Pi.add_apply] using
          M.tendsto_add a b)
    rw [h, map_add]
  map_mul' a b := by
    have h : normMatrixCStarCoronaMk (fun n ↦ X n) (seq M (a * b)) =
        normMatrixCStarCoronaMk (fun n ↦ X n) (seq M a * seq M b) :=
      ShulmanTrace.coronaQuotient_eq_of_tendsto_zero (fun n ↦ X n) _ _ (by
        simpa only [seq_apply, lp.infty_coeFn_mul, Pi.mul_apply] using
          M.tendsto_mul a b)
    rw [h, map_mul]
  map_star' a := by
    have h : normMatrixCStarCoronaMk (fun n ↦ X n) (seq M (star a)) =
        normMatrixCStarCoronaMk (fun n ↦ X n) (star (seq M a)) :=
      ShulmanTrace.coronaQuotient_eq_of_tendsto_zero (fun n ↦ X n) _ _ (by
        simpa only [seq_apply, lp.star_apply, Matrix.star_eq_conjTranspose] using
          M.tendsto_star a)
    rw [h, ← normMatrixCStarCorona_star_mk]

@[simp] theorem coronaHom_apply
    (M : NormCoronaAsymptoticLift.Model (X := X) A) (a : A) :
    coronaHom M a = normMatrixCStarCoronaMk (fun n ↦ X n) (seq M a) :=
  rfl

/-- Exact limsup norm recovery makes the corona homomorphism faithful. -/
theorem coronaHom_injective_of_normRecovery
    (M : NormCoronaAsymptoticLift.Model (X := X) A)
    (hrecover : ∀ a : A,
      Filter.limsup (fun n ↦ ‖M.map n a‖) atTop = ‖a‖) :
    Function.Injective (coronaHom M) := by
  intro a b hab
  have hzero : coronaHom M (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hnorm : ‖a - b‖ = 0 := by
    calc
      ‖a - b‖ = Filter.limsup (fun n ↦ ‖M.map n (a - b)‖) atTop :=
        (hrecover (a - b)).symm
      _ = ‖normMatrixCStarCoronaMk (fun n ↦ X n) (seq M (a - b))‖ := by
        change Filter.limsup (fun n ↦ ‖M.map n (a - b)‖) atTop =
          ‖Ideal.Quotient.mk
            (nullMatrixSequenceIdeal (fun n ↦ X n) cofinite)
            (seq M (a - b))‖
        simpa only [seq_apply, Nat.cofinite_eq_atTop] using
          (norm_filterMatrixCorona_mk_eq_limsup (fun n ↦ X n) cofinite
            (seq M (a - b))).symm
      _ = 0 := by rw [← coronaHom_apply, hzero, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- A norm-recovering asymptotic model supplies the repository's bare MF
embedding datum. -/
theorem hasMFEmbedding_of_normRecovery
    (M : NormCoronaAsymptoticLift.Model (X := X) A)
    (hrecover : ∀ a : A,
      Filter.limsup (fun n ↦ ‖M.map n a‖) atTop = ‖a‖)
    (hpos : ∀ n, 0 < Fintype.card (X n))
    (hmono : StrictMono (fun n ↦ Fintype.card (X n))) :
    HasMFEmbedding A :=
  ⟨X, fun _ ↦ inferInstance, hpos, hmono, coronaHom M,
    coronaHom_injective_of_normRecovery M hrecover⟩

end

end AsymptoticModelMFEmbedding
end GroupApproximation
