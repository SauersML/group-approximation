import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.PadBlock
import GroupApproximation.Meta.AxiomGuard

/-!
# The section `σ : J → St_4(L)` over the vertex stabilizer (lane sk-leavitt-05)

Khanh (arXiv:2609.08428), proof of Theorem 5.1: `σ(j(b, H)) = ℓ(H) · x_1(b)`, mirrored to the
index `last`.  For `g = [[H, 0], [b, 1]] ∈ J` put

  `sectionJ g = liftGL H · rowVec b`.

* `sectionJ` is a homomorphism.  With `b(gk) = b(g) H(k) + b(k)` (`bottomRow_mul`),
  `ℓ(H(k)) x(b(g) H(k)) = x(b(g)) ℓ(H(k))` (`liftGL_mul_rowVec`, lane 02) and additivity of `rowVec`:
  `ℓ(H_g H_k) x(b_g H_k) x(b_k) = ℓ(H_g) x(b_g) ℓ(H_k) x(b_k)`.
* `projection_comp_sectionJ`: `projection ∘ sectionJ = subtype`.  It follows from
  `projection ℓ(H) = [[H, 0], [0, 1]]`, `projection x(b) = [[1, 0], [b, 1]]` and
  `padHom_mul_rowMat`.
* `sectionJ_eq_rowVec_mul_liftGL`: the lane's form `x_last(b') · ℓ(H)` with `b' = b H⁻¹`, matching
  the factorization `g = [[1, 0], [b', 1]] · [[H, 0], [0, 1]]`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open scoped Matrix

local notation "𝓛" => GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)

noncomputable section

/-- **The section `σ : J →* St_4(L)`**, `σ(j(b, H)) = ℓ(H) · x_last(b)`. -/
def sectionJ (h : EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement)
    (hrow : RowVecStabConjStatement) : Criterion.vertexStab →* St 4 𝓛 :=
  MonoidHom.mk' (fun g => liftGL h (blockUnits g) * rowVec (bottomRow g)) fun g k => by
    show liftGL h (blockUnits (g * k)) * rowVec (bottomRow (g * k)) =
      liftGL h (blockUnits g) * rowVec (bottomRow g) *
        (liftGL h (blockUnits k) * rowVec (bottomRow k))
    rw [map_mul, map_mul, bottomRow_mul, rowVec_add]
    have hk := liftGL_mul_rowVec h hrow (blockUnits k) (bottomRow g)
    rw [blockUnits_val] at hk
    rw [mul_assoc, ← mul_assoc (liftGL h (blockUnits k)), hk]
    simp only [mul_assoc]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.sectionJ

theorem sectionJ_apply (h : EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement)
    (hrow : RowVecStabConjStatement) (g : Criterion.vertexStab) :
    sectionJ h hrow g = liftGL h (blockUnits g) * rowVec (bottomRow g) :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.sectionJ_apply

/-- The lane's form `σ(g) = x_last(b H⁻¹) · ℓ(H)`. -/
theorem sectionJ_eq_rowVec_mul_liftGL
    (h : EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement)
    (hrow : RowVecStabConjStatement) (g : Criterion.vertexStab) :
    sectionJ h hrow g =
      rowVec (bottomRow g ᵥ* (((blockUnits g)⁻¹ : (Matrix (Fin 3) (Fin 3) 𝓛)ˣ) :
        Matrix (Fin 3) (Fin 3) 𝓛)) * liftGL h (blockUnits g) := by
  have hk := liftGL_mul_rowVec h hrow (blockUnits g)
    (bottomRow g ᵥ* (((blockUnits g)⁻¹ : (Matrix (Fin 3) (Fin 3) 𝓛)ˣ) : Matrix (Fin 3) (Fin 3) 𝓛))
  rw [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one] at hk
  rw [sectionJ_apply]
  exact hk

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.sectionJ_eq_rowVec_mul_liftGL

/-- **`σ` is a section:** `projection (σ g) = g` in `GL_4(L)`. -/
theorem projection_sectionJ (h : EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement)
    (hrow : RowVecStabConjStatement) (g : Criterion.vertexStab) :
    ((projection (sectionJ h hrow g) : elementaryGroup (Fin 4) 𝓛) : (Matrix (Fin 4) (Fin 4) 𝓛)ˣ) =
      (g : (Matrix (Fin 4) (Fin 4) 𝓛)ˣ) := by
  apply Units.ext
  change emat (projection (sectionJ h hrow g)) = mat g
  rw [sectionJ_apply, map_mul, emat_mul, projection_rowVec_val, emat, projection_liftGL_val]
  exact padHom_mul_rowMat g

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.projection_sectionJ

/-- **`projection ∘ σ = subtype`.** -/
theorem projection_comp_sectionJ
    (h : EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement)
    (hrow : RowVecStabConjStatement) :
    ((elementaryGroup (Fin 4) 𝓛).subtype.comp (projection (I := Fin 4) (R := 𝓛))).comp
        (sectionJ h hrow) = (Criterion.vertexStab).subtype :=
  MonoidHom.ext fun g => projection_sectionJ h hrow g

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.projection_comp_sectionJ

/-- **Endpoint (conditional on lane 02's formula).**  From `stab (K₂(3, L)) = ⊥` and
`RowVecStabConjStatement`: a homomorphism `σ : J → St_4(L)` with `projection ∘ σ = subtype` and
`σ(j(b, H)) = ℓ(H) · x_last(b)`. -/
theorem exists_vertexSection_of_rowVecStabConj
    (h : EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement)
    (hrow : RowVecStabConjStatement) :
    ∃ σ : Criterion.vertexStab →* St 4 𝓛,
      ((elementaryGroup (Fin 4) 𝓛).subtype.comp (projection (I := Fin 4) (R := 𝓛))).comp σ =
          (Criterion.vertexStab).subtype ∧
        ∀ g, σ g = liftGL h (blockUnits g) * rowVec (bottomRow g) :=
  ⟨sectionJ h hrow, projection_comp_sectionJ h hrow, sectionJ_apply h hrow⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.exists_vertexSection_of_rowVecStabConj

end

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift
