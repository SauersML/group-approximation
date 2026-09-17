import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.Interfaces
import GroupApproximation.Meta.AxiomGuard

/-!
# The lift `ℓ : GL_3(L) → St_4(L)` (lane sk-leavitt-05)

Khanh (arXiv:2609.08428), proof of Theorem 5.1.  Over `L = L_{𝔽₂}(1,2)` we have
`GL_3(L) = E_3(L) ≅ St_3(L) ⧸ K₂(3, L)` (`BinaryLeavitt.elementaryGroup_eq_top`,
`SteinbergBasic.quotientK2Equiv`).  Suppose `stab : St_3(L) → St_4(L)` kills `K₂(3, L)`
(`EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement`).  Then `stab` factors through
the quotient, which gives

  `liftGL h = stab ∘ (St_3 ⧸ K₂ ≃* E_3)⁻¹ ∘ (GL_3 = E_3)`.

Proved here:

* `liftGL_projection`: `ℓ (projection g) = stab g`;
* `projection_liftGL`: `projection (ℓ M) = elementaryStab (M)`, i.e. `[[M, 0], [0, 1]]`;
* `liftGL_mul_rowVec`: `ℓ M · x_last(b M) = x_last(b) · ℓ M`, from lane 02's conjugation formula
  (`RowVecStabConjStatement`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open scoped Matrix

local notation "𝓛" => GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)

noncomputable section

/-- `GL_3(L) = E_3(L)`, as a homomorphism into the elementary subgroup. -/
def toElementary3 : (Matrix (Fin 3) (Fin 3) 𝓛)ˣ →* elementaryGroup (Fin 3) 𝓛 :=
  (MonoidHom.id (Matrix (Fin 3) (Fin 3) 𝓛)ˣ).codRestrict (elementaryGroup (Fin 3) 𝓛) fun M => by
    rw [GroupApproximation.BinaryLeavitt.elementaryGroup_eq_top (ZMod 2) 3 (by norm_num)]
    exact Subgroup.mem_top _

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.toElementary3

/-- **The lift `ℓ : GL_3(L) → St_4(L)`.**  It is well defined because `stab` kills `K₂(3, L)`. -/
def liftGL (h : EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement) :
    (Matrix (Fin 3) (Fin 3) 𝓛)ˣ →* St 4 𝓛 :=
  (QuotientGroup.lift (K2 (Fin 3) 𝓛) (stab 3 𝓛) (Subgroup.map_eq_bot_iff.mp h)).comp
    ((quotientK2Equiv (I := Fin 3) (R := 𝓛)).symm.toMonoidHom.comp toElementary3)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.liftGL

/-- `ℓ` extends `stab` along the projection `St_3(L) → E_3(L) = GL_3(L)`. -/
theorem liftGL_projection (h : EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement)
    (g : St 3 𝓛) :
    liftGL h ((projection g : elementaryGroup (Fin 3) 𝓛) : (Matrix (Fin 3) (Fin 3) 𝓛)ˣ) =
      stab 3 𝓛 g := by
  have hq : (quotientK2Equiv (I := Fin 3) (R := 𝓛)).symm
      (toElementary3 ((projection g : elementaryGroup (Fin 3) 𝓛) :
        (Matrix (Fin 3) (Fin 3) 𝓛)ˣ)) = (g : St 3 𝓛 ⧸ K2 (Fin 3) 𝓛) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  change QuotientGroup.lift (K2 (Fin 3) 𝓛) (stab 3 𝓛) (Subgroup.map_eq_bot_iff.mp h)
      ((quotientK2Equiv (I := Fin 3) (R := 𝓛)).symm
        (toElementary3 ((projection g : elementaryGroup (Fin 3) 𝓛) :
          (Matrix (Fin 3) (Fin 3) 𝓛)ˣ))) = stab 3 𝓛 g
  rw [hq]
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.liftGL_projection

/-- **`projection ∘ ℓ` is the padding `M ↦ [[M, 0], [0, 1]]`.** -/
theorem projection_liftGL (h : EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement)
    (M : (Matrix (Fin 3) (Fin 3) 𝓛)ˣ) :
    projection (liftGL h M) = elementaryStab 3 𝓛 (toElementary3 M) := by
  obtain ⟨g, hg⟩ := projection_surjective (I := Fin 3) (R := 𝓛) (toElementary3 M)
  have hM : ((projection g : elementaryGroup (Fin 3) 𝓛) : (Matrix (Fin 3) (Fin 3) 𝓛)ˣ) = M :=
    congrArg Subtype.val hg
  have hl : liftGL h M = stab 3 𝓛 g := by
    rw [← hM, liftGL_projection]
  rw [hl, projection_stab, hg]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.projection_liftGL

/-- The unit-group form of `projection_liftGL`. -/
theorem projection_liftGL_val
    (h : EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement)
    (M : (Matrix (Fin 3) (Fin 3) 𝓛)ˣ) :
    ((projection (liftGL h M) : elementaryGroup (Fin 4) 𝓛) : (Matrix (Fin 4) (Fin 4) 𝓛)ˣ) =
      ElementaryPadding.padUnitHom Fin.castSuccEmb M := by
  rw [projection_liftGL]
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.projection_liftGL_val

/-- **`ℓ` normalizes the bottom-row vectors:** `ℓ M · x_last(b M) = x_last(b) · ℓ M`.  This is
lane 02's `stab_conj_rowVec` with `g` a Steinberg lift of `M`. -/
theorem liftGL_mul_rowVec (h : EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement)
    (hrow : RowVecStabConjStatement) (M : (Matrix (Fin 3) (Fin 3) 𝓛)ˣ) (b : Fin 3 → 𝓛) :
    liftGL h M * rowVec (b ᵥ* (M : Matrix (Fin 3) (Fin 3) 𝓛)) = rowVec b * liftGL h M := by
  obtain ⟨g, hg⟩ := projection_surjective (I := Fin 3) (R := 𝓛) (toElementary3 M)
  have hM : ((projection g : elementaryGroup (Fin 3) 𝓛) : (Matrix (Fin 3) (Fin 3) 𝓛)ˣ) = M :=
    congrArg Subtype.val hg
  have hl : liftGL h M = stab 3 𝓛 g := by
    rw [← hM, liftGL_projection]
  have hconj := hrow g (b ᵥ* (M : Matrix (Fin 3) (Fin 3) 𝓛))
  have hinv : ((((projection g)⁻¹ : elementaryGroup (Fin 3) 𝓛) : (Matrix (Fin 3) (Fin 3) 𝓛)ˣ) :
      Matrix (Fin 3) (Fin 3) 𝓛) =
        ((M⁻¹ : (Matrix (Fin 3) (Fin 3) 𝓛)ˣ) : Matrix (Fin 3) (Fin 3) 𝓛) := by
    rw [Subgroup.coe_inv, hM]
  rw [hinv, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one] at hconj
  rw [hl]
  exact mul_inv_eq_iff_eq_mul.mp hconj

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.liftGL_mul_rowVec

end

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift
