import GroupApproximation.Analysis.CStarStatePullback
import GroupApproximation.Analysis.CStarMinTensorNorm

/-!
# Functoriality of the minimal tensor norm along surjections

## What this module proves

For a **surjective** unital ⋆-homomorphism `q : B →⋆ₐ[ℂ] Q` and any
C⋆-algebra `C`, the algebraic map `q ⊗ id : B ⊙ C → Q ⊙ C` is contractive
for the canonical minimal tensor norms:

  `minTensorNorm ((q ⊗ id) x) ≤ minTensorNorm x`.

The proof is the state-pullback argument of `CStarStatePullback`, run at the
tensor level.  Every term of the supremum defining the left side is the norm
of `spatialHom (gnsRep ψ ∘ q, gnsRep ρ) x` for a pair of states `(ψ, ρ)` of
`Q` and `C`; the GNS comparison isometry of the pullback state `ψ ∘ q` is
*onto* because `q` is, it intertwines the two representations of `B`, and
conjugation by a surjective isometry preserves operator norms -- so the term
equals the `(ψ ∘ q, ρ)` term of the supremum defining the right side.

## Why surjectivity is genuinely used

Twice: the comparison isometry has dense range only because `q` maps `B`
*onto* a dense subset of the pre-GNS space of `ψ`, and the operator-norm
transfer needs every vector of the target Hilbert space in the range.  For
non-surjective `q` -- in particular the inclusion of an ideal, the left leg
of the exactness sequence -- the corresponding statement is
Takesaki-adjacent and is **not** proved here or anywhere in this
development; the docstring of `CStarMinTensorNorm` records it as open.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `SO.16` and
`RE.05` remain **MISSING**.  With this module the right leg of the textbook
exactness sequence exists at the level of norms; the ideal leg and the
`IsExact` predicate remain.
-/

namespace GroupApproximation
namespace CStarTensor

open CStarState
open scoped TensorProduct InnerProductSpace

universe u v w

variable {B : Type u} {Q : Type v} {C : Type w}
  [CStarAlgebra B] [CStarAlgebra Q] [CStarAlgebra C]
  [Nontrivial B] [Nontrivial Q] [Nontrivial C]

/-! ## The composite representation -/

/-- The GNS representation of a state of `Q`, composed with
`q : B →⋆ₐ[ℂ] Q`: a ⋆-representation of `B` on the GNS space of `ψ`. -/
noncomputable def gnsCompRep (ψ : State Q) (q : B →⋆ₐ[ℂ] Q) :
    StarRep B ψ.GNSSpace where
  hom := ((ψ.gnsRep).hom).comp q.toAlgHom
  isAdjoint_star b := by
    show IsAdjoint ((ψ.gnsRep).hom (q b)) ((ψ.gnsRep).hom (q (star b)))
    rw [map_star]
    exact (ψ.gnsRep).isAdjoint_star (q b)

omit [Nontrivial B] in
@[simp] theorem gnsCompRep_hom_apply (ψ : State Q) (q : B →⋆ₐ[ℂ] Q) (b : B) :
    (gnsCompRep ψ q).hom b = (ψ.gnsRep).hom (q b) := rfl

omit [Nontrivial B] in
/-- Composing the spatial representation with `q ⊗ id` is the spatial
representation of the composite. -/
theorem spatialHom_map_eq (ψ : State Q) (ρ : State C) (q : B →⋆ₐ[ℂ] Q)
    (x : B ⊗[ℂ] C) :
    spatialHom ψ.gnsRep ρ.gnsRep
        (Algebra.TensorProduct.map q.toAlgHom (AlgHom.id ℂ C) x)
      = spatialHom (gnsCompRep ψ q) ρ.gnsRep x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b c =>
      rw [Algebra.TensorProduct.map_tmul, spatialHom_tmul, spatialHom_tmul]
      rfl
  | add y z hy hz =>
      rw [map_add, map_add, map_add, hy, hz]

/-! ## Operator-norm transfer along a surjective isometry -/

/-- Conjugation by a surjective linear isometry preserves operator norms:
if `T₂ ∘ W = W ∘ T₁` with `W` a surjective isometry, then `‖T₂‖ = ‖T₁‖`. -/
theorem opNorm_eq_of_intertwine {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (W : E →ₗᵢ[ℂ] F) (hW : Function.Surjective W)
    (T₁ : E →L[ℂ] E) (T₂ : F →L[ℂ] F)
    (h : ∀ ξ : E, T₂ (W ξ) = W (T₁ ξ)) : ‖T₂‖ = ‖T₁‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T₁) fun η => ?_
    obtain ⟨ξ, rfl⟩ := hW η
    rw [h ξ, W.norm_map, W.norm_map]
    exact T₁.le_opNorm ξ
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T₂) fun ξ => ?_
    calc ‖T₁ ξ‖ = ‖W (T₁ ξ)‖ := (W.norm_map _).symm
      _ = ‖T₂ (W ξ)‖ := by rw [h ξ]
      _ ≤ ‖T₂‖ * ‖W ξ‖ := T₂.le_opNorm _
      _ = ‖T₂‖ * ‖ξ‖ := by rw [W.norm_map]

/-! ## The tensor-level comparison -/

section Surjective

variable (ψ : State Q) (ρ : State C) (q : B →⋆ₐ[ℂ] Q)

/-- The GNS comparison map, as a linear isometry. -/
noncomputable def gnsCompIsometry :
    (ψ.comp q).GNSSpace →ₗᵢ[ℂ] ψ.GNSSpace where
  toLinearMap := (gnsComp ψ q).toLinearMap
  norm_map' := norm_gnsComp_apply ψ q

@[simp] theorem gnsCompIsometry_apply (ζ : (ψ.comp q).GNSSpace) :
    gnsCompIsometry ψ q ζ = gnsComp ψ q ζ := rfl

/-- The tensor-level comparison isometry `V ⊗ id`. -/
noncomputable def tensorCompIsometry :
    ((ψ.comp q).GNSSpace ⊗[ℂ] ρ.GNSSpace) →ₗᵢ[ℂ]
      (ψ.GNSSpace ⊗[ℂ] ρ.GNSSpace) :=
  TensorProduct.mapIsometry (gnsCompIsometry ψ q) (LinearIsometry.id)

theorem tensorCompIsometry_tmul (h : (ψ.comp q).GNSSpace)
    (k : ρ.GNSSpace) :
    tensorCompIsometry ψ ρ q (h ⊗ₜ[ℂ] k) = gnsComp ψ q h ⊗ₜ[ℂ] k := by
  show TensorProduct.mapIsometry _ _ (h ⊗ₜ[ℂ] k) = _
  rw [TensorProduct.mapIsometry_apply, TensorProduct.map_tmul]
  rfl

/-- For surjective `q` the tensor-level comparison is surjective. -/
theorem tensorCompIsometry_surjective (hq : Function.Surjective q) :
    Function.Surjective (tensorCompIsometry ψ ρ q) := by
  have h1 : Function.Surjective (gnsComp ψ q) := gnsComp_surjective ψ q hq
  have h := TensorProduct.map_surjective
    (g := ((gnsComp ψ q).toLinearMap : (ψ.comp q).GNSSpace →ₗ[ℂ] ψ.GNSSpace))
    (g' := (LinearMap.id : ρ.GNSSpace →ₗ[ℂ] ρ.GNSSpace))
    h1 Function.surjective_id
  intro η
  obtain ⟨ξ, hξ⟩ := h η
  refine ⟨ξ, ?_⟩
  show TensorProduct.mapIsometry _ _ ξ = η
  rw [TensorProduct.mapIsometry_apply]
  exact hξ

/-- **The tensor-level intertwining**: `V ⊗ id` carries the spatial
representation of the pullback pair to the spatial representation of the
composite pair. -/
theorem tensorCompIsometry_intertwines (x : B ⊗[ℂ] C)
    (ζ : (ψ.comp q).GNSSpace ⊗[ℂ] ρ.GNSSpace) :
    spatialHom (gnsCompRep ψ q) ρ.gnsRep x (tensorCompIsometry ψ ρ q ζ)
      = tensorCompIsometry ψ ρ q
          (spatialHom ((ψ.comp q).gnsRep) ρ.gnsRep x ζ) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b c =>
      induction ζ using TensorProduct.induction_on with
      | zero => simp
      | tmul h k =>
          rw [spatialHom_tmul, spatialHom_tmul, tensorCompIsometry_tmul,
            TensorProduct.mapL_tmul, TensorProduct.mapL_tmul,
            tensorCompIsometry_tmul]
          rw [gnsCompRep_hom_apply]
          rw [gnsComp_intertwines]
      | add ζ₁ ζ₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | add y z hy hz =>
      rw [map_add, map_add, add_apply, add_apply, hy, hz, map_add]

/-- Per state pair, the spatial seminorm of the image equals the spatial
seminorm of the original at the pulled-back pair. -/
theorem spatialNorm_map_eq (hq : Function.Surjective q) (x : B ⊗[ℂ] C) :
    spatialNorm ψ.gnsRep ρ.gnsRep
        (Algebra.TensorProduct.map q.toAlgHom (AlgHom.id ℂ C) x)
      = spatialNorm ((ψ.comp q).gnsRep) ρ.gnsRep x := by
  rw [spatialNorm_apply, spatialNorm_apply, spatialHom_map_eq]
  exact opNorm_eq_of_intertwine (tensorCompIsometry ψ ρ q)
    (tensorCompIsometry_surjective ψ ρ q hq)
    (spatialHom ((ψ.comp q).gnsRep) ρ.gnsRep x)
    (spatialHom (gnsCompRep ψ q) ρ.gnsRep x)
    (tensorCompIsometry_intertwines ψ ρ q x)

end Surjective

/-! ## The main inequality -/

/-- **Contractivity of `q ⊗ id` on minimal tensor norms, for surjective
`q`**: every term of the image's supremum is a term of the original's
supremum at the pulled-back state pair. -/
theorem minTensorNorm_map_le (q : B →⋆ₐ[ℂ] Q)
    (hq : Function.Surjective q) (x : B ⊗[ℂ] C) :
    minTensorNorm (Algebra.TensorProduct.map q.toAlgHom (AlgHom.id ℂ C) x)
      ≤ minTensorNorm x := by
  rw [minTensorNorm_apply]
  refine ciSup_le fun p => ?_
  have h := spatialNorm_map_eq p.1 p.2 q hq x
  calc spatialNorm p.1.gnsRep p.2.gnsRep
        (Algebra.TensorProduct.map q.toAlgHom (AlgHom.id ℂ C) x)
      = spatialNorm ((p.1.comp q).gnsRep) p.2.gnsRep x := h
    _ ≤ minTensorNorm x := by
        rw [minTensorNorm_apply]
        exact le_ciSup (bddAbove_spatialNorm_gnsRep x)
          ((p.1.comp q, p.2) : State B × State C)

end CStarTensor
end GroupApproximation
