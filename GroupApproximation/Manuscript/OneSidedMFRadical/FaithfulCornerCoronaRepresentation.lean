import GroupApproximation.Analysis.CStarStateGNS
import GroupApproximation.Analysis.OmegaCoronaKazhdanProjection
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# A faithful Hilbert-space representation of the corner corona

The manuscript chooses a faithful Hilbert-space representation of its unital
corner corona.  This file supplies that choice internally.  For a nontrivial
unital C-star algebra `A`, take the Hilbert `ℓ²`-sum of the GNS spaces of all
states of `A` and let `A` act diagonally.  The state-indexed GNS family already
constructed in `CStarStateGNS` is jointly norm-attaining, so the diagonal
representation is faithful.

The final declarations specialize the construction to the precise omega
matrix corona used in the unchanged normal-Kazhdan proof.  Its nontriviality
is the unconditional theorem `OmegaCoronaKazhdanProjection.coronaNontrivial`.
-/

namespace GroupApproximation
namespace CStarState

open scoped ENNReal InnerProductSpace

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

/-- The Hilbert direct sum of the GNS spaces of all states of `A`. -/
abbrev UniversalGNSSpace (A : Type u) [CStarAlgebra A] [Nontrivial A] :=
  lp (fun φ : State A ↦ φ.GNSSpace) 2

/-- The pointwise diagonal action, before its norm bound is bundled. -/
noncomputable def universalGNSLinear (a : A) :
    UniversalGNSSpace A →ₗ[ℂ] UniversalGNSSpace A where
  toFun x := ⟨fun φ ↦ (φ.gnsRep).hom a (x φ), by
    refine Memℓp.mono' ((lp.memℓp x).const_smul (‖a‖ : ℂ)) fun φ ↦ ?_
    calc
      ‖(φ.gnsRep).hom a (x φ)‖
          ≤ ‖(φ.gnsRep).hom a‖ * ‖x φ‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖a‖ * ‖x φ‖ := by
        exact mul_le_mul_of_nonneg_right (φ.norm_gnsRep_apply_le a)
          (norm_nonneg _)
      _ = ‖((‖a‖ : ℂ) •
          (⇑x : ∀ φ : State A, φ.GNSSpace)) φ‖ := by
        rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg a)]⟩
  map_add' x y := by
    refine lp.ext (funext fun φ ↦ ?_)
    change (φ.gnsRep).hom a (x φ + y φ) =
      (φ.gnsRep).hom a (x φ) + (φ.gnsRep).hom a (y φ)
    rw [map_add]
  map_smul' c x := by
    refine lp.ext (funext fun φ ↦ ?_)
    change (φ.gnsRep).hom a (c • x φ) = c • (φ.gnsRep).hom a (x φ)
    rw [map_smul]

@[simp]
theorem universalGNSLinear_apply (a : A) (x : UniversalGNSSpace A)
    (φ : State A) :
    universalGNSLinear a x φ = (φ.gnsRep).hom a (x φ) := rfl

/-- The diagonal GNS action is bounded by the original C-star norm. -/
noncomputable def universalGNSOperator (a : A) :
    UniversalGNSSpace A →L[ℂ] UniversalGNSSpace A :=
  LinearMap.mkContinuous (universalGNSLinear a) ‖a‖ fun x ↦ by
    calc
      ‖universalGNSLinear a x‖
          ≤ ‖(‖a‖ : ℂ) • x‖ := by
            refine lp.norm_mono (by norm_num) fun φ ↦ ?_
            rw [universalGNSLinear_apply, lp.coeFn_smul, Pi.smul_apply,
              norm_smul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (norm_nonneg a)]
            calc
              ‖(φ.gnsRep).hom a (x φ)‖
                  ≤ ‖(φ.gnsRep).hom a‖ * ‖x φ‖ :=
                    ContinuousLinearMap.le_opNorm _ _
              _ ≤ ‖a‖ * ‖x φ‖ :=
                mul_le_mul_of_nonneg_right (φ.norm_gnsRep_apply_le a)
                  (norm_nonneg _)
      _ = ‖a‖ * ‖x‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg a)]

@[simp]
theorem universalGNSOperator_apply (a : A) (x : UniversalGNSSpace A)
    (φ : State A) :
    universalGNSOperator a x φ = (φ.gnsRep).hom a (x φ) := rfl

/-- The direct-sum action as a unital star-algebra homomorphism. -/
noncomputable def universalGNSStarAlgHom :
    A →⋆ₐ[ℂ] (UniversalGNSSpace A →L[ℂ] UniversalGNSSpace A) where
  toFun := universalGNSOperator
  map_one' := by
    refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun φ ↦ ?_)
    change (φ.gnsRep).hom 1 (x φ) = x φ
    rw [map_one]
    rfl
  map_mul' a b := by
    refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun φ ↦ ?_)
    change (φ.gnsRep).hom (a * b) (x φ) =
      (φ.gnsRep).hom a ((φ.gnsRep).hom b (x φ))
    rw [map_mul]
    rfl
  map_zero' := by
    refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun φ ↦ ?_)
    change (φ.gnsRep).hom 0 (x φ) = 0
    rw [map_zero]
    rfl
  map_add' a b := by
    refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun φ ↦ ?_)
    change (φ.gnsRep).hom (a + b) (x φ) =
      (φ.gnsRep).hom a (x φ) + (φ.gnsRep).hom b (x φ)
    rw [map_add]
    rfl
  commutes' c := by
    refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun φ ↦ ?_)
    change (φ.gnsRep).hom (algebraMap ℂ A c) (x φ) = c • x φ
    rw [(φ.gnsRep).hom.commutes]
    rfl
  map_star' a := by
    rw [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun φ ↦ ?_
    simpa using (φ.gnsRep).isAdjoint_star (star a) (x φ) (y φ)

@[simp]
theorem universalGNSStarAlgHom_apply (a : A) (x : UniversalGNSSpace A)
    (φ : State A) :
    universalGNSStarAlgHom a x φ = (φ.gnsRep).hom a (x φ) := rfl

/-- The universal direct-sum GNS representation has zero kernel. -/
theorem universalGNSStarAlgHom_eq_zero_iff (a : A) :
    universalGNSStarAlgHom a = 0 ↔ a = 0 := by
  constructor
  · intro ha
    obtain ⟨φ, hφ⟩ := exists_state_norm_le_gnsRep a
    have hcoordinate : (φ.gnsRep).hom a = 0 := by
      classical
      refine ContinuousLinearMap.ext fun ξ ↦ ?_
      have hvector := congrArg
        (fun T : UniversalGNSSpace A →L[ℂ] UniversalGNSSpace A ↦
          T (lp.single 2 φ ξ)) ha
      have hcoord := congrArg (fun z : UniversalGNSSpace A ↦ z φ) hvector
      simpa using hcoord
    rw [hcoordinate, norm_zero] at hφ
    apply norm_eq_zero.mp
    exact le_antisymm hφ (norm_nonneg a)
  · rintro rfl
    exact map_zero _

/-- **Generic Gelfand--Naimark theorem in the repository's representation
format:** every nontrivial unital complex C-star algebra acts faithfully on
the Hilbert sum of the GNS spaces of all its states. -/
theorem universalGNSStarAlgHom_injective :
    Function.Injective (universalGNSStarAlgHom (A := A)) := by
  intro a b hab
  rw [← sub_eq_zero]
  rw [← universalGNSStarAlgHom_eq_zero_iff]
  rw [map_sub, hab, sub_self]

end

end CStarState

namespace Manuscript
namespace OneSidedMFRadical

open OmegaCoronaKazhdanProjection VectorOmegaAction

noncomputable section

/-- The omega matrix corona is nontrivial; named as an instance so its
universal GNS Hilbert sum can be used in declaration types. -/
noncomputable instance cornerCoronaNontrivial
    (Y : ℕ → FiniteModel) (ω : Ultrafilter ℕ) [∀ n, Nonempty (Y n)] :
    Nontrivial (FilterMatrixCStarCorona (Idx Y) (ω : Filter ℕ)) :=
  coronaNontrivial Y ω

/-- The faithful Hilbert space used for the manuscript's omega matrix corona. -/
abbrev CornerCoronaFaithfulSpace (Y : ℕ → FiniteModel)
    (ω : Ultrafilter ℕ) [∀ n, Nonempty (Y n)] :=
  CStarState.UniversalGNSSpace
    (FilterMatrixCStarCorona (Idx Y) (ω : Filter ℕ))

/-- The manuscript's omega matrix corona represented faithfully on a Hilbert
space, with no external representation-existence hypothesis. -/
noncomputable def cornerCoronaFaithfulRepresentation
    (Y : ℕ → FiniteModel) (ω : Ultrafilter ℕ) [∀ n, Nonempty (Y n)] :
    FilterMatrixCStarCorona (Idx Y) (ω : Filter ℕ) →⋆ₐ[ℂ]
      (CornerCoronaFaithfulSpace Y ω →L[ℂ] CornerCoronaFaithfulSpace Y ω) := by
  exact CStarState.universalGNSStarAlgHom

/-- The preceding concrete corner-corona representation is faithful. -/
theorem cornerCoronaFaithfulRepresentation_injective
    (Y : ℕ → FiniteModel) (ω : Ultrafilter ℕ) [∀ n, Nonempty (Y n)] :
    Function.Injective (cornerCoronaFaithfulRepresentation Y ω) := by
  exact CStarState.universalGNSStarAlgHom_injective

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
