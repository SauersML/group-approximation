import GroupApproximation.Analysis.CStarC0DirectSumSeparable
import GroupApproximation.Analysis.STW22AntipodalBlockData
import GroupApproximation.Analysis.STW22ActualTraceSpaces
import GroupApproximation.Analysis.STW22RealProjectiveBlockSeparable
import GroupApproximation.Analysis.STW22RealProjectiveBlockTypeI

/-!
# The concrete STW base algebra is the ordinary unitization

`STW22ActualTraceSpaces.BaseAlgebra D` was defined as the closed subalgebra of
bounded block sequences which converge in norm to a scalar.  This file gives
the explicit star-algebra equivalence with
`Unitization ℂ (CStarC0DirectSum.C0DirectSum D)` and transports separability.
-/

namespace GroupApproximation
namespace STW22BaseAlgebraUnitization

open Filter Topology PolarLiftingGeneralCStar
open CStarC0DirectSum UniformTracialSequenceCompletion
open UniformTracialTwoNullIdeal STW22ActualTraceSpaces

noncomputable section

universe u

variable (D : ℕ → Type u) [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)]

/-- Include a norm-null block sequence into the concrete scalar-plus-`c₀`
base algebra. -/
def c0ToBase : C0DirectSum D →⋆ₙₐ[ℂ] BaseAlgebra D where
  toFun b := ⟨b.1, (mem_baseAlgebra_iff b.1).2 ⟨0, by
    have hb : IsNullCStarSequence D atTop b.1 := b.2
    change Tendsto (fun n ↦ ‖b.1 n‖) atTop (nhds 0) at hb
    change Tendsto (fun n ↦ ‖b.1 n - algebraMap ℂ (D n) 0‖) atTop (nhds 0)
    simpa only [map_zero, sub_zero] using hb⟩⟩
  map_zero' := by apply Subtype.ext; rfl
  map_add' _ _ := by apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl
  map_star' _ := by apply Subtype.ext; rfl

@[simp] theorem c0ToBase_apply (b : C0DirectSum D) :
    ((c0ToBase D b : BaseAlgebra D) : BoundedCStarSequence D) = b.1 := rfl

/-- The universal unitization map into the concrete base algebra. -/
def unitizationToBase :
    Unitization ℂ (C0DirectSum D) →⋆ₐ[ℂ] BaseAlgebra D :=
  Unitization.starLift (c0ToBase D)

@[simp] theorem unitizationToBase_inr (b : C0DirectSum D) :
    unitizationToBase D (b : Unitization ℂ (C0DirectSum D)) = c0ToBase D b := by
  simp [unitizationToBase]

@[simp] theorem unitizationToBase_inl (c : ℂ) :
    unitizationToBase D (Unitization.inl c) = algebraMap ℂ (BaseAlgebra D) c := by
  simpa [Unitization.algebraMap_eq_inl] using (unitizationToBase D).commutes c

theorem unitizationToBase_surjective : Function.Surjective (unitizationToBase D) := by
  rintro x
  obtain ⟨c, hc⟩ := (mem_baseAlgebra_iff (x : BoundedCStarSequence D)).1 x.2
  let b : C0DirectSum D :=
    ⟨(x : BoundedCStarSequence D) -
      algebraMap ℂ (BoundedCStarSequence D) c, by
        change Tendsto (fun n ↦
          ‖(x : BoundedCStarSequence D) n - algebraMap ℂ (D n) c‖)
          atTop (nhds 0)
        exact hc⟩
  refine ⟨Unitization.inl c + (b : Unitization ℂ (C0DirectSum D)), ?_⟩
  apply Subtype.ext
  apply lp.ext
  funext n
  simp [b, unitizationToBase]
  change algebraMap ℂ (D n) c +
      ((x : BoundedCStarSequence D) n - algebraMap ℂ (D n) c) =
    (x : BoundedCStarSequence D) n
  abel

theorem unitizationToBase_injective : Function.Injective (unitizationToBase D) := by
  intro x y hxy
  induction x using Unitization.ind with
  | inl_add_inr c b =>
    induction y using Unitization.ind with
    | inl_add_inr c' b' =>
      have hseq :
          algebraMap ℂ (BoundedCStarSequence D) c + b.1 =
            algebraMap ℂ (BoundedCStarSequence D) c' + b'.1 := by
        have hbase :
            algebraMap ℂ (BaseAlgebra D) c + c0ToBase D b =
              algebraMap ℂ (BaseAlgebra D) c' + c0ToBase D b' := by
          simpa only [map_add, unitizationToBase_inl,
            unitizationToBase_inr] using hxy
        have this := congrArg
          (fun z : BaseAlgebra D ↦ (z : BoundedCStarSequence D)) hbase
        change
          algebraMap ℂ (BoundedCStarSequence D) c + b.1 =
            algebraMap ℂ (BoundedCStarSequence D) c' + b'.1 at this
        exact this
      have hb : b.1 ∈ twoNullIdeal (normTracialTwoGauge D) := by
        rw [twoNullIdeal_normTracialTwoGauge]
        exact b.2
      have hb' : b'.1 ∈ twoNullIdeal (normTracialTwoGauge D) := by
        rw [twoNullIdeal_normTracialTwoGauge]
        exact b'.2
      have hcc' : c = c' :=
        scalar_unique (normTracialTwoGauge D) hb hb' hseq
      subst c'
      have hbb' : b = b' := by
        apply Subtype.ext
        exact add_left_cancel hseq
      subst b'
      rfl

/-- The concrete scalar-plus-`c₀` model and the ordinary minimal unitization
are the same C-star algebra up to an explicit star-algebra equivalence. -/
def unitizationEquivBase :
    Unitization ℂ (C0DirectSum D) ≃⋆ₐ[ℂ] BaseAlgebra D :=
  StarAlgEquiv.ofBijective (unitizationToBase D)
    ⟨unitizationToBase_injective D, unitizationToBase_surjective D⟩

/-- Type I transports from the ordinary unitization to the concrete
scalar-plus-`c₀` base model along the explicit equivalence. -/
theorem isTypeI_baseAlgebra_of_unitization
    (hU : STW22.IsTypeI (Unitization ℂ (C0DirectSum D))) :
    STW22.IsTypeI (BaseAlgebra D) := by
  intro H _ _ _ π hπ T hT
  let ρ : Unitization ℂ (C0DirectSum D) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
    π.comp (unitizationToBase D)
  have hρ : STW22.IsIrreducibleRep ρ := by
    refine ⟨?_, ?_⟩
    · obtain ⟨a, ha⟩ := hπ.1
      obtain ⟨b, hb⟩ := unitizationToBase_surjective D a
      refine ⟨b, ?_⟩
      change π (unitizationToBase D b) ≠ 0
      rw [hb]
      exact ha
    · intro M hM
      apply hπ.2 M
      refine ⟨hM.1, ?_⟩
      intro a x hx
      obtain ⟨b, hb⟩ := unitizationToBase_surjective D a
      have h := hM.2 b x hx
      change π (unitizationToBase D b) x ∈ M at h
      rw [hb] at h
      exact h
  obtain ⟨b, hb⟩ := hU H ρ hρ T hT
  refine ⟨unitizationToBase D b, ?_⟩
  exact hb

/-- The actual STW base algebra is separable whenever its coordinate blocks
are separable. -/
theorem separableSpace_baseAlgebra
    [∀ n, TopologicalSpace.SeparableSpace (D n)] :
    TopologicalSpace.SeparableSpace (BaseAlgebra D) := by
  letI : TopologicalSpace.SeparableSpace
      (Unitization ℂ (C0DirectSum D)) :=
    separableSpace_unitization_c0DirectSum D
  have hcontinuous : Continuous (unitizationToBase D) := by
    exact (LipschitzWith.of_dist_le_mul (K := 1) fun x y ↦ by
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
      change ‖unitizationToBase D x - unitizationToBase D y‖ ≤ ‖x - y‖
      calc
        ‖unitizationToBase D x - unitizationToBase D y‖ =
            ‖unitizationToBase D (x - y)‖ := by
              congr 1
              exact (map_sub (unitizationToBase D) x y).symm
        _ ≤ ‖x - y‖ := NonUnitalStarAlgHom.norm_apply_le
          (unitizationToBase D) (x - y)).continuous
  exact (unitizationToBase_surjective D).denseRange.separableSpace hcontinuous

/-! ## The concrete counterexample base -/

/-- The actual scalar-plus-`c₀` base built from arbitrary real-projective
blocks is type I. -/
theorem isTypeI_baseAlgebra_realProjectiveBlocks (d s : ℕ → ℕ) :
    STW22.IsTypeI (BaseAlgebra
      (fun n ↦ STW22.RealProjectiveBlock (d n) (s n))) :=
  isTypeI_baseAlgebra_of_unitization
    (fun n ↦ STW22.RealProjectiveBlock (d n) (s n))
    (STW22.isTypeI_unitization_c0DirectSum_realProjectiveBlocks d s)

/-- The same concrete base is separable. -/
theorem separableSpace_baseAlgebra_realProjectiveBlocks (d s : ℕ → ℕ) :
    TopologicalSpace.SeparableSpace (BaseAlgebra
      (fun n ↦ STW22.RealProjectiveBlock (d n) (s n))) :=
  separableSpace_baseAlgebra
    (fun n ↦ STW22.RealProjectiveBlock (d n) (s n))

/-- The literal base algebra used by the antipodal counterexample is type I. -/
theorem isTypeI_baseAlgebra_antipodalCounterexampleBlock :
    STW22.IsTypeI (BaseAlgebra STW22.AntipodalCounterexampleBlock) :=
  isTypeI_baseAlgebra_realProjectiveBlocks
    STW22.antipodalBlockDimension STW22.antipodalBlockSize

/-- The literal base algebra used by the antipodal counterexample is
separable. -/
theorem separableSpace_baseAlgebra_antipodalCounterexampleBlock :
    TopologicalSpace.SeparableSpace
      (BaseAlgebra STW22.AntipodalCounterexampleBlock) :=
  separableSpace_baseAlgebra_realProjectiveBlocks
    STW22.antipodalBlockDimension STW22.antipodalBlockSize

end

end STW22BaseAlgebraUnitization
end GroupApproximation
