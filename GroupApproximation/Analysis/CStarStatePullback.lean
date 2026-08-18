import GroupApproximation.Analysis.CStarStateGNS

/-!
# Pulling back states, and comparing their GNS representations

## What this module builds

For a unital ⋆-homomorphism `q : B →⋆ₐ[ℂ] Q` of C⋆-algebras:

* `State.comp` -- the pullback `ψ ∘ q` of a state, a state because
  ⋆-homomorphisms of C⋆-algebras are automatically contractive
  (`NonUnitalStarAlgHom.norm_apply_le`);
* `gnsComp` -- the canonical comparison map
  `GNS(ψ ∘ q) → GNS(ψ)`, induced by `q` itself between the pre-GNS spaces,
  **norm-preserving** because
  `⟪b, b'⟫_{ψ∘q} = (ψ∘q)(b⋆b') = ψ((q b)⋆(q b')) = ⟪q b, q b'⟫_ψ`;
* `gnsComp_intertwines` -- the comparison map carries the GNS representation
  of the pullback state to the GNS representation of `ψ` composed with `q`:
  `gnsComp ∘ π_{ψ∘q}(b) = π_ψ(q b) ∘ gnsComp`;
* for **surjective** `q`, `gnsComp_surjective`: the comparison map is onto,
  because it is already onto at the pre-GNS level and an isometry of a
  complete space has closed range.

## Why this is the engine of `⊗_min` functoriality

For surjective `q`, the intertwining unitary identifies the GNS
representation of any pullback state with the composite representation, so a
supremum over states of `Q` of composite-representation norms is dominated
by the supremum over states of `B` -- which is exactly the contractivity of
`q ⊗ id` for the canonical minimal tensor norms, the right leg of the
exactness short exact sequence.  That tensor-level statement lives in the
next module; this one supplies every analytic ingredient.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `SO.16` and
`RE.05` remain **MISSING**.
-/

namespace GroupApproximation
namespace CStarState

open scoped ComplexOrder InnerProductSpace
open UniformSpace

universe u v

variable {B : Type u} {Q : Type v} [CStarAlgebra B] [CStarAlgebra Q]
  [Nontrivial B] [Nontrivial Q]

/-! ## ⋆-homomorphisms as continuous linear maps -/

/-- A unital ⋆-homomorphism of C⋆-algebras, as a continuous linear map: the
automatic contractivity of ⋆-homomorphisms supplies the bound. -/
noncomputable def starAlgHomCLM (q : B →⋆ₐ[ℂ] Q) : B →L[ℂ] Q :=
  LinearMap.mkContinuous q.toAlgHom.toLinearMap 1 fun b => by
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le q b

omit [Nontrivial B] [Nontrivial Q] in
@[simp] theorem starAlgHomCLM_apply (q : B →⋆ₐ[ℂ] Q) (b : B) :
    starAlgHomCLM q b = q b := rfl

/-! ## The pullback state -/

/-- **The pullback of a state along a unital ⋆-homomorphism.**  Unitality is
`q 1 = 1`; the contraction bound composes the state's bound with the
automatic contractivity of `q`. -/
noncomputable def State.comp (ψ : State Q) (q : B →⋆ₐ[ℂ] Q) : State B where
  toCLM := ψ.toCLM.comp (starAlgHomCLM q)
  map_one := by
    show ψ.toCLM (starAlgHomCLM q 1) = 1
    rw [starAlgHomCLM_apply, _root_.map_one, ψ.map_one]
  norm_le := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun b => ?_
    rw [one_mul]
    have h1 : ‖ψ.toCLM (starAlgHomCLM q b)‖ ≤ ‖starAlgHomCLM q b‖ := by
      have h := ψ.toCLM.le_opNorm (starAlgHomCLM q b)
      have h2 : ‖ψ.toCLM‖ * ‖starAlgHomCLM q b‖
          ≤ 1 * ‖starAlgHomCLM q b‖ := by
        gcongr
        exact ψ.norm_le
      rw [one_mul] at h2
      exact h.trans h2
    refine h1.trans ?_
    rw [starAlgHomCLM_apply]
    exact NonUnitalStarAlgHom.norm_apply_le q b

omit [Nontrivial B] [Nontrivial Q] in
@[simp] theorem State.comp_apply (ψ : State Q) (q : B →⋆ₐ[ℂ] Q) (b : B) :
    (ψ.comp q).toCLM b = ψ.toCLM (q b) := rfl

/-! ## The GNS comparison map -/

section Pullback

noncomputable local instance (priority := 0) : PartialOrder B :=
  CStarAlgebra.spectralOrder B

noncomputable local instance (priority := 0) : StarOrderedRing B :=
  CStarAlgebra.spectralOrderedRing B

noncomputable local instance (priority := 0) : PartialOrder Q :=
  CStarAlgebra.spectralOrder Q

noncomputable local instance (priority := 0) : StarOrderedRing Q :=
  CStarAlgebra.spectralOrderedRing Q

variable (ψ : State Q) (q : B →⋆ₐ[ℂ] Q)

/-- The pre-GNS comparison map: `q` itself, read from the pre-GNS space of
the pullback state to the pre-GNS space of the state. -/
noncomputable def preGNSComp :
    (ψ.comp q).toPositive.PreGNS →ₗ[ℂ] ψ.toPositive.PreGNS :=
  ψ.toPositive.toPreGNS.toLinearMap ∘ₗ q.toAlgHom.toLinearMap ∘ₗ
    (ψ.comp q).toPositive.ofPreGNS.toLinearMap

@[simp] theorem preGNSComp_apply (x : (ψ.comp q).toPositive.PreGNS) :
    preGNSComp ψ q x
      = ψ.toPositive.toPreGNS (q ((ψ.comp q).toPositive.ofPreGNS x)) := rfl

/-- The comparison map preserves the pre-GNS norm: the two seminorms compute
the same number, `(ψ (q (b⋆ b))).re`. -/
theorem norm_preGNSComp (x : (ψ.comp q).toPositive.PreGNS) :
    ‖preGNSComp ψ q x‖ = ‖x‖ := by
  rw [PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.preGNS_norm_def,
    preGNSComp_apply, PositiveLinearMap.ofPreGNS_toPreGNS]
  have harg : star (q ((ψ.comp q).toPositive.ofPreGNS x)) *
        q ((ψ.comp q).toPositive.ofPreGNS x)
      = q (star ((ψ.comp q).toPositive.ofPreGNS x) *
          ((ψ.comp q).toPositive.ofPreGNS x)) := by
    rw [← map_star, ← map_mul]
  have h : ψ.toPositive
        (star (q ((ψ.comp q).toPositive.ofPreGNS x)) *
          q ((ψ.comp q).toPositive.ofPreGNS x))
      = (ψ.comp q).toPositive
        (star ((ψ.comp q).toPositive.ofPreGNS x) *
          ((ψ.comp q).toPositive.ofPreGNS x)) := by
    rw [State.toPositive_apply, State.toPositive_apply, State.comp_apply,
      harg]
  rw [h]

/-- For surjective `q`, the comparison map is onto at the pre-GNS level. -/
theorem preGNSComp_surjective (hq : Function.Surjective q) :
    Function.Surjective (preGNSComp ψ q) := by
  intro y
  obtain ⟨b, hb⟩ := hq (ψ.toPositive.ofPreGNS y)
  refine ⟨(ψ.comp q).toPositive.toPreGNS b, ?_⟩
  rw [preGNSComp_apply, PositiveLinearMap.ofPreGNS_toPreGNS, hb,
    PositiveLinearMap.toPreGNS_ofPreGNS]

/-- The pre-GNS comparison map as a continuous linear map. -/
noncomputable def preGNSCompL :
    (ψ.comp q).toPositive.PreGNS →L[ℂ] ψ.toPositive.PreGNS :=
  LinearMap.mkContinuous (preGNSComp ψ q) 1 fun x => by
    rw [one_mul, norm_preGNSComp]

@[simp] theorem preGNSCompL_apply (x : (ψ.comp q).toPositive.PreGNS) :
    preGNSCompL ψ q x = preGNSComp ψ q x := rfl

/-- **The GNS comparison map**: the completion of the pre-GNS comparison,
from the GNS space of the pullback state to the GNS space of the state. -/
noncomputable def gnsComp : (ψ.comp q).GNSSpace →L[ℂ] ψ.GNSSpace :=
  (preGNSCompL ψ q).completion

/-- The comparison map is norm-preserving. -/
theorem norm_gnsComp_apply (ζ : (ψ.comp q).GNSSpace) :
    ‖gnsComp ψ q ζ‖ = ‖ζ‖ := by
  induction ζ using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq (continuous_norm.comp (gnsComp ψ q).continuous)
        continuous_norm
  | ih x =>
      show ‖gnsComp ψ q ((↑x : (ψ.comp q).toPositive.GNS))‖
          = ‖((↑x : (ψ.comp q).toPositive.GNS))‖
      have h3 : ‖gnsComp ψ q ((↑x : (ψ.comp q).toPositive.GNS))‖
          = ‖preGNSCompL ψ q x‖ := by
        rw [show gnsComp ψ q ((↑x : (ψ.comp q).toPositive.GNS))
              = (↑(preGNSCompL ψ q x) : ψ.toPositive.GNS) from
            ContinuousLinearMap.completion_apply_coe _ _]
        exact UniformSpace.Completion.norm_coe _
      have h4 : ‖((↑x : (ψ.comp q).toPositive.GNS))‖ = ‖x‖ :=
        UniformSpace.Completion.norm_coe _
      rw [h3, h4]
      exact norm_preGNSComp ψ q x

/-- The comparison map is an isometry. -/
theorem isometry_gnsComp : Isometry (gnsComp ψ q) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_gnsComp_apply ψ q)

/-- **For surjective `q` the comparison map is onto**: its range contains the
dense image of the pre-GNS space, and an isometry out of a complete space has
closed range. -/
theorem gnsComp_surjective (hq : Function.Surjective q) :
    Function.Surjective (gnsComp ψ q) := by
  have hsub : Set.range ((↑) : ψ.toPositive.PreGNS → ψ.toPositive.GNS)
      ⊆ Set.range (gnsComp ψ q) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := preGNSComp_surjective ψ q hq y
    refine ⟨(↑x : (ψ.comp q).toPositive.GNS), ?_⟩
    have h1 : gnsComp ψ q ((↑x : (ψ.comp q).toPositive.GNS))
        = (↑(preGNSCompL ψ q x) : ψ.toPositive.GNS) :=
      ContinuousLinearMap.completion_apply_coe _ _
    rw [h1]
    exact congrArg _ hx
  have hdense : Dense (Set.range (gnsComp ψ q)) :=
    UniformSpace.Completion.denseRange_coe.mono hsub
  have hclosed : IsClosed (Set.range (gnsComp ψ q)) :=
    (isometry_gnsComp ψ q).isClosedEmbedding.isClosed_range
  have huniv : Set.range (gnsComp ψ q) = Set.univ := by
    rw [← hclosed.closure_eq]
    exact hdense.closure_eq
  intro ζ
  have : ζ ∈ Set.range (gnsComp ψ q) := by rw [huniv]; trivial
  exact this

/-- **The intertwining identity**: the comparison map carries the GNS
representation of the pullback state to the GNS representation of `ψ`
composed with `q`. -/
theorem gnsComp_intertwines (b : B) (ζ : (ψ.comp q).GNSSpace) :
    gnsComp ψ q (((ψ.comp q).gnsRep).hom b ζ)
      = (ψ.gnsRep).hom (q b) (gnsComp ψ q ζ) := by
  induction ζ using UniformSpace.Completion.induction_on with
  | hp =>
      refine isClosed_eq ?_ ?_
      · exact (gnsComp ψ q).continuous.comp
          (((ψ.comp q).gnsRep).hom b).continuous
      · exact ((ψ.gnsRep).hom (q b)).continuous.comp
          (gnsComp ψ q).continuous
  | ih x =>
      show (preGNSCompL ψ q).completion
          (((ψ.comp q).toPositive.leftMulMapPreGNS b).completion ↑x)
        = (ψ.toPositive.leftMulMapPreGNS (q b)).completion
            ((preGNSCompL ψ q).completion ↑x)
      rw [ContinuousLinearMap.completion_apply_coe,
        ContinuousLinearMap.completion_apply_coe,
        ContinuousLinearMap.completion_apply_coe,
        ContinuousLinearMap.completion_apply_coe]
      congr 1
      show preGNSComp ψ q
          ((ψ.comp q).toPositive.toPreGNS
            (b * (ψ.comp q).toPositive.ofPreGNS x))
        = ψ.toPositive.toPreGNS
            (q b * ψ.toPositive.ofPreGNS (preGNSComp ψ q x))
      rw [preGNSComp_apply, PositiveLinearMap.ofPreGNS_toPreGNS, map_mul,
        preGNSComp_apply, PositiveLinearMap.ofPreGNS_toPreGNS]

end Pullback

end CStarState
end GroupApproximation
