import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.Section
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.Main
import GroupApproximation.Meta.AxiomGuard

/-!
# Closing the lane-02 interface (lane sk-leavitt-05)

Lane sk-leavitt-02 is on disk (`LeavittK2/RowColumn`).  Its row vector
`LeavittK2.rowVec b = ∏ᵢ x_{last, castSucc i}(b i)` agrees at rank three with the local
`VertexLift.rowVec b = x_{3,0}(b 0) · x_{3,1}(b 1) · x_{3,2}(b 2)` (`leavittRowVec_eq`, by
splitting off one coordinate at a time with `LeavittK2.rowVec_split`).  So lane 02's
`stab_conj_rowVec_coe` proves `RowVecStabConjStatement` (`rowVecStabConj`), and the section
`σ : J →* St_4(L)` depends only on `stab (K₂(3, L)) = ⊥`.

Endpoint: `exists_vertexSection_of_stabKernelThreeTrivial`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open scoped Matrix

local notation "𝓛" => GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)

noncomputable section

/-- Lane 02's row vector is the local one at rank three. -/
theorem leavittRowVec_eq (b : Fin 3 → 𝓛) : LeavittK2.rowVec b = VertexLift.rowVec b := by
  have hz : Function.update (Function.update (Function.update b 0 (0 : 𝓛)) 1 0) 2 0 =
      (0 : Fin 3 → 𝓛) := by
    funext k
    fin_cases k <;> simp [Function.update_apply]
  have h1 : Function.update b 0 (0 : 𝓛) 1 = b 1 :=
    Function.update_of_ne (show (1 : Fin 3) ≠ 0 by decide) (0 : 𝓛) b
  have h2 : Function.update (Function.update b 0 (0 : 𝓛)) 1 0 2 = b 2 := by
    rw [Function.update_of_ne (show (2 : Fin 3) ≠ 1 by decide),
      Function.update_of_ne (show (2 : Fin 3) ≠ 0 by decide)]
  rw [LeavittK2.rowVec_split b 0, LeavittK2.rowVec_split (Function.update b 0 0) 1,
    LeavittK2.rowVec_split (Function.update (Function.update b 0 0) 1 0) 2, hz,
    LeavittK2.rowVec_zero, mul_one, h1, h2, VertexLift.rowVec, mul_assoc]
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.leavittRowVec_eq

/-- **The lane-02 interface holds**: `RowVecStabConjStatement` is lane 02's
`stab_conj_rowVec_coe` at `n = 3`, `R = L`. -/
theorem rowVecStabConj : RowVecStabConjStatement := by
  intro g b
  have h := LeavittK2.stab_conj_rowVec_coe (n := 3) (R := 𝓛) g b
  rw [leavittRowVec_eq, leavittRowVec_eq] at h
  exact h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.rowVecStabConj

/-- **The section `σ : J →* St_4(L)`**, depending only on `stab (K₂(3, L)) = ⊥`. -/
def vertexSection (h : EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement) :
    Criterion.vertexStab →* St 4 𝓛 :=
  sectionJ h rowVecStabConj

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.vertexSection

theorem vertexSection_apply (h : EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement)
    (g : Criterion.vertexStab) :
    vertexSection h g = liftGL h (blockUnits g) * VertexLift.rowVec (bottomRow g) :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.vertexSection_apply

/-- **`projection ∘ σ = subtype`.** -/
theorem projection_comp_vertexSection
    (h : EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement) :
    ((elementaryGroup (Fin 4) 𝓛).subtype.comp (projection (I := Fin 4) (R := 𝓛))).comp
        (vertexSection h) = (Criterion.vertexStab).subtype :=
  projection_comp_sectionJ h rowVecStabConj

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.projection_comp_vertexSection

/-- **Endpoint of lane sk-leavitt-05.**  From `stab (K₂(3, L)) = ⊥`: a homomorphism
`σ : J → St_4(L)` with `projection ∘ σ = subtype` and `σ(j(b, H)) = ℓ(H) · x_last(b)`. -/
theorem exists_vertexSection_of_stabKernelThreeTrivial
    (h : EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement) :
    ∃ σ : Criterion.vertexStab →* St 4 𝓛,
      ((elementaryGroup (Fin 4) 𝓛).subtype.comp (projection (I := Fin 4) (R := 𝓛))).comp σ =
          (Criterion.vertexStab).subtype ∧
        ∀ g, σ g = liftGL h (blockUnits g) * VertexLift.rowVec (bottomRow g) :=
  ⟨vertexSection h, projection_comp_vertexSection h, vertexSection_apply h⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.exists_vertexSection_of_stabKernelThreeTrivial

end

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift
