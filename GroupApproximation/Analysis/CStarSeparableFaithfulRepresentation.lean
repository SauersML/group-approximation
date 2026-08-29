import GroupApproximation.Analysis.CStarStateGNS
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# A separable C-star algebra is faithfully represented on a countable GNS sum

`Manuscript/OneSidedMFRadical/FaithfulCornerCoronaRepresentation` builds the
universal GNS representation — the Hilbert sum over **all** states of `A` — and
proves it faithful.  That is Gelfand--Naimark in the repository's format, and
nothing here re-proves it.  What it does not give is a *separable* Hilbert
space: its index set is `State A`, which is as large as the dual ball.

This module runs the same construction over an arbitrary family of states, and
then shows that for a separable `A` a **countable** family already separates
points.  The two halves are independent:

* `familyGNSStarAlgHom` is the diagonal action on `lp (fun i ↦ (ψ i).GNSSpace) 2`
  for any `ψ : ι → State A`, with `familyGNSStarAlgHom_injective` reducing
  faithfulness to the separation hypothesis on the family.  Every clause is the
  corresponding clause of the state's own GNS representation read coordinatewise,
  exactly as in the universal case; the adjoint clause is the one with content,
  and it is `lp.inner_eq_tsum` together with `StarRep.isAdjoint_star`.
* `exists_countable_separating_states` produces the family.  The engine is
  `CStarState.exists_state_norm_le_gnsRep`, which says the norm of an element is
  *attained* by some state's GNS representation rather than merely approximated.
  Index the states by a countable dense subset, one norm-attaining state per
  element; a nonzero `a` is within `‖a‖/2` of some `b` in that subset, and then
  `‖π_b a‖ ≥ ‖π_b b‖ - ‖π_b (b - a)‖ ≥ ‖b‖ - ‖b - a‖ > 0`, so that single
  coordinate already separates `a` from `0`.

## What this is for, and what it does not yet do

`ShulmanFill.SeparableFaithfulRepresentationStatement` asks for a faithful
representation on a separable Hilbert space **in `Type 0`**.  This module
supplies the representation and the countable index; the Hilbert space it
produces still lives in the universe of `A`.  Two further steps are needed for
that statement, and neither is in Mathlib at the pinned revision — where
`SeparableSpace` does not occur in `Mathlib/Analysis/InnerProductSpace/` at all:
separability of the sum, and the descent of a separable Hilbert space to
`ℓ²` over a countable index, which needs "a separable Hilbert space has a
countable Hilbert basis".  Those are deliberately not attempted here.
-/

namespace GroupApproximation
namespace CStarState

open scoped InnerProductSpace

noncomputable section

universe u v

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]
variable {ι : Type v}

/-! ## The diagonal action of a family of GNS representations -/

/-- The Hilbert direct sum of the GNS spaces of a family of states. -/
abbrev FamilyGNSSpace (ψ : ι → State A) : Type (max u v) :=
  lp (fun i : ι ↦ (ψ i).GNSSpace) 2

variable (ψ : ι → State A)

/-- The pointwise diagonal action, before its norm bound is bundled. -/
def familyGNSLinear (a : A) : FamilyGNSSpace ψ →ₗ[ℂ] FamilyGNSSpace ψ where
  toFun x := ⟨fun i ↦ ((ψ i).gnsRep).hom a (x i), by
    refine Memℓp.mono' ((lp.memℓp x).const_smul (‖a‖ : ℂ)) fun i ↦ ?_
    calc
      ‖((ψ i).gnsRep).hom a (x i)‖
          ≤ ‖((ψ i).gnsRep).hom a‖ * ‖x i‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖a‖ * ‖x i‖ :=
        mul_le_mul_of_nonneg_right ((ψ i).norm_gnsRep_apply_le a)
          (norm_nonneg _)
      _ = ‖((‖a‖ : ℂ) •
          (⇑x : ∀ i : ι, (ψ i).GNSSpace)) i‖ := by
        rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg a)]⟩
  map_add' x y := by
    refine lp.ext (funext fun i ↦ ?_)
    change ((ψ i).gnsRep).hom a (x i + y i) =
      ((ψ i).gnsRep).hom a (x i) + ((ψ i).gnsRep).hom a (y i)
    rw [map_add]
  map_smul' c x := by
    refine lp.ext (funext fun i ↦ ?_)
    change ((ψ i).gnsRep).hom a (c • x i) = c • ((ψ i).gnsRep).hom a (x i)
    rw [map_smul]

@[simp] theorem familyGNSLinear_apply (a : A) (x : FamilyGNSSpace ψ) (i : ι) :
    familyGNSLinear ψ a x i = ((ψ i).gnsRep).hom a (x i) := rfl

/-- The diagonal action is bounded by the C-star norm of `a`. -/
def familyGNSOperator (a : A) : FamilyGNSSpace ψ →L[ℂ] FamilyGNSSpace ψ :=
  LinearMap.mkContinuous (familyGNSLinear ψ a) ‖a‖ fun x ↦ by
    calc
      ‖familyGNSLinear ψ a x‖
          ≤ ‖(‖a‖ : ℂ) • x‖ := by
            refine lp.norm_mono (by norm_num) fun i ↦ ?_
            rw [familyGNSLinear_apply, lp.coeFn_smul, Pi.smul_apply,
              norm_smul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (norm_nonneg a)]
            calc
              ‖((ψ i).gnsRep).hom a (x i)‖
                  ≤ ‖((ψ i).gnsRep).hom a‖ * ‖x i‖ :=
                    ContinuousLinearMap.le_opNorm _ _
              _ ≤ ‖a‖ * ‖x i‖ :=
                mul_le_mul_of_nonneg_right ((ψ i).norm_gnsRep_apply_le a)
                  (norm_nonneg _)
      _ = ‖a‖ * ‖x‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg a)]

@[simp] theorem familyGNSOperator_apply (a : A) (x : FamilyGNSSpace ψ) (i : ι) :
    familyGNSOperator ψ a x i = ((ψ i).gnsRep).hom a (x i) := rfl

/-- **The diagonal GNS action of a family of states**, as a unital
`*`-homomorphism.  This is `universalGNSStarAlgHom` of
`Manuscript/OneSidedMFRadical/FaithfulCornerCoronaRepresentation` with the index
set left free instead of being all of `State A`. -/
def familyGNSStarAlgHom :
    A →⋆ₐ[ℂ] (FamilyGNSSpace ψ →L[ℂ] FamilyGNSSpace ψ) where
  toFun := familyGNSOperator ψ
  map_one' := by
    refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun i ↦ ?_)
    change ((ψ i).gnsRep).hom 1 (x i) = x i
    rw [map_one]
    rfl
  map_mul' a b := by
    refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun i ↦ ?_)
    change ((ψ i).gnsRep).hom (a * b) (x i) =
      ((ψ i).gnsRep).hom a (((ψ i).gnsRep).hom b (x i))
    rw [map_mul]
    rfl
  map_zero' := by
    refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun i ↦ ?_)
    change ((ψ i).gnsRep).hom 0 (x i) = 0
    rw [map_zero]
    rfl
  map_add' a b := by
    refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun i ↦ ?_)
    change ((ψ i).gnsRep).hom (a + b) (x i) =
      ((ψ i).gnsRep).hom a (x i) + ((ψ i).gnsRep).hom b (x i)
    rw [map_add]
    rfl
  commutes' c := by
    refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun i ↦ ?_)
    change ((ψ i).gnsRep).hom (algebraMap ℂ A c) (x i) = c • x i
    rw [((ψ i).gnsRep).hom.commutes]
    rfl
  map_star' a := by
    rw [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun i ↦ ?_
    simpa using ((ψ i).gnsRep).isAdjoint_star (star a) (x i) (y i)

@[simp] theorem familyGNSStarAlgHom_apply (a : A) (x : FamilyGNSSpace ψ)
    (i : ι) :
    familyGNSStarAlgHom ψ a x i = ((ψ i).gnsRep).hom a (x i) := rfl

/-- Every coordinate of a vanishing diagonal action vanishes: test on the
single-coordinate vectors. -/
theorem gnsRep_eq_zero_of_familyGNSStarAlgHom_eq_zero (a : A)
    (ha : familyGNSStarAlgHom ψ a = 0) (i : ι) :
    ((ψ i).gnsRep).hom a = 0 := by
  classical
  refine ContinuousLinearMap.ext fun ξ ↦ ?_
  have hvector := congrArg
    (fun T : FamilyGNSSpace ψ →L[ℂ] FamilyGNSSpace ψ ↦ T (lp.single 2 i ξ)) ha
  have hcoord := congrArg (fun z : FamilyGNSSpace ψ ↦ z i) hvector
  simpa using hcoord

/-- **The diagonal action of a separating family is faithful.** -/
theorem familyGNSStarAlgHom_injective
    (hsep : ∀ a : A, a ≠ 0 → ∃ i, ((ψ i).gnsRep).hom a ≠ 0) :
    Function.Injective (familyGNSStarAlgHom ψ) := by
  intro a b hab
  by_contra hne
  obtain ⟨i, hi⟩ := hsep (a - b) (sub_ne_zero.mpr hne)
  refine hi (gnsRep_eq_zero_of_familyGNSStarAlgHom_eq_zero ψ (a - b) ?_ i)
  rw [map_sub, hab, sub_self]

end

/-! ## A countable separating family, for a separable algebra -/

section Countable

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

/-- **A separable C-star algebra has a countable separating family of states.**

The norm of every element is attained by some state's GNS representation
(`exists_state_norm_le_gnsRep`), so it is enough to attach one such state to
each point of a countable dense subset: a nonzero `a` lies within `‖a‖/2` of
some `b` there, and then

    `‖π_b a‖ ≥ ‖π_b b‖ - ‖π_b (b - a)‖ ≥ ‖b‖ - ‖b - a‖`
    `        > ‖a‖/2 - ‖a‖/2 = 0` ,

using that `π_b` is contractive.  So that one coordinate already separates. -/
theorem exists_countable_separating_states
    [TopologicalSpace.SeparableSpace A] :
    ∃ (s : Set A) (_ : s.Countable) (ψ : s → State A),
      ∀ a : A, a ≠ 0 → ∃ i, ((ψ i).gnsRep).hom a ≠ 0 := by
  classical
  obtain ⟨s, hs_count, hs_dense⟩ := TopologicalSpace.exists_countable_dense A
  refine ⟨s, hs_count,
    fun b ↦ (exists_state_norm_le_gnsRep (b : A)).choose, ?_⟩
  intro a ha
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  obtain ⟨b, hbs, hb⟩ :=
    hs_dense.exists_dist_lt a (by linarith : (0 : ℝ) < ‖a‖ / 2)
  refine ⟨⟨b, hbs⟩, ?_⟩
  set φ := (exists_state_norm_le_gnsRep b).choose with hφdef
  have hφ : ‖b‖ ≤ ‖(φ.gnsRep).hom b‖ :=
    (exists_state_norm_le_gnsRep b).choose_spec
  have hdist : ‖b - a‖ < ‖a‖ / 2 := by
    rw [norm_sub_rev]
    rwa [dist_eq_norm] at hb
  have hbnorm : ‖a‖ / 2 < ‖b‖ := by
    have := norm_sub_norm_le a b
    have h2 : ‖a - b‖ < ‖a‖ / 2 := by rwa [dist_eq_norm] at hb
    linarith
  have hsub : ‖(φ.gnsRep).hom (b - a)‖ ≤ ‖b - a‖ :=
    φ.norm_gnsRep_apply_le (b - a)
  intro hzero
  have hbz : (φ.gnsRep).hom b = (φ.gnsRep).hom (b - a) := by
    rw [map_sub, hzero, sub_zero]
  have : ‖b‖ ≤ ‖b - a‖ := by
    rw [hbz] at hφ
    exact hφ.trans hsub
  linarith

end Countable

end CStarState
end GroupApproximation
