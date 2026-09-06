import GroupApproximation.Analysis.LIXLimitMatrixTransport
import GroupApproximation.Analysis.LIXStageAlgebra
import GroupApproximation.Meta.AxiomGuard

/-!
# The second Fubini: `M_ι(C(X, ℂ)) ≃⋆ₐ[ℂ] C(X, M_ι(ℂ))`

`Analysis/LIXLimitMatrixFlatten` handles one of the two identifications the LIX witness needs,
`M₂(M₂(A)) ≅ M₄(A)`.  This file handles the other, and it is a different Fubini: matrices over
continuous functions against continuous functions into matrices.  The null-homotopy of
`diag (u, 1)` is built pointwise over the base, so it lives on the right; `CStarMat n` over a
stage algebra unfolds towards the left.

All the mathematics is already in `cs-stages`' files.  `STW59.ofFunctionMatrix` and
`STW59.toFunctionMatrix` are mutually inverse — both round trips are `rfl` — and
`ofFunctionMatrix_mul`, `_add`, `_star`, `_smul`, `_one` and `_zero` are proved there.  What was
missing is only the bundling, and the choice of which side of the `Matrix` / `CStarMatrix`
synonym to state it on.

That choice is the one decision here.  Stating the source as `CStarMatrix ι ι C(X, ℂ)` rather
than `Matrix ι ι C(X, ℂ)` costs nothing — the two are the same type — but it makes the source a
genuine C⋆-algebra for compact `X`, so `unitaryHom` and hence
`unitaryHom_mem_unitaryComponentOne` apply and `U₀` membership transports in both directions.
Stated over `Matrix` it would not, because Mathlib puts the C⋆-structure on `CStarMatrix` only.
-/

namespace GroupApproximation

namespace LIX

noncomputable section

open scoped ComplexOrder

attribute [local instance 100000] GroupApproximation.LIX.instSpectralPartialOrder
                                  GroupApproximation.LIX.instSpectralStarOrderedRing

section Equiv

variable {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The section–matrix identification**, bundled: a matrix of continuous scalar functions is
the same thing as a continuous matrix-valued function.  Every field is one of `cs-stages`'
lemmas; the source is written at `CStarMatrix` so that both sides carry the C⋆-structure. -/
def sectionMatrixEquiv : CStarMatrix ι ι C(X, ℂ) ≃⋆ₐ[ℂ] STW59.SectionAlgebra X ι where
  toFun M := STW59.ofFunctionMatrix M
  invFun a := STW59.toFunctionMatrix a
  left_inv M := STW59.toFunctionMatrix_ofFunctionMatrix M
  right_inv a := STW59.ofFunctionMatrix_toFunctionMatrix a
  map_mul' M N := STW59.ofFunctionMatrix_mul M N
  map_add' M N := STW59.ofFunctionMatrix_add M N
  map_star' M := STW59.ofFunctionMatrix_star M
  map_smul' c M := STW59.ofFunctionMatrix_smul c M

@[simp] theorem sectionMatrixEquiv_apply (M : CStarMatrix ι ι C(X, ℂ)) :
    sectionMatrixEquiv M = STW59.ofFunctionMatrix M := rfl

@[simp] theorem sectionMatrixEquiv_symm_apply (a : STW59.SectionAlgebra X ι) :
    (sectionMatrixEquiv (X := X) (ι := ι)).symm a = STW59.toFunctionMatrix a := rfl

@[simp] theorem sectionMatrixEquiv_apply_entry (M : CStarMatrix ι ι C(X, ℂ)) (x : X) (i j : ι) :
    sectionMatrixEquiv M x i j = M i j x := rfl

end Equiv

/-! ### Transport of `U₀` across the identification -/

section Transport

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The identification as a unital ⋆-homomorphism. -/
def sectionMatrixHom : CStarMatrix ι ι C(X, ℂ) →⋆ₐ[ℂ] STW59.SectionAlgebra X ι :=
  (sectionMatrixEquiv (X := X) (ι := ι)).toStarAlgHom

/-- Its inverse as a unital ⋆-homomorphism. -/
def sectionMatrixSymmHom : STW59.SectionAlgebra X ι →⋆ₐ[ℂ] CStarMatrix ι ι C(X, ℂ) :=
  (sectionMatrixEquiv (X := X) (ι := ι)).symm.toStarAlgHom

/-- A null-homotopic matrix of functions gives a null-homotopic matrix-valued function. -/
theorem sectionMatrix_mem_unitaryComponentOne {v : unitary (CStarMatrix ι ι C(X, ℂ))}
    (hv : v ∈ unitaryComponentOne (CStarMatrix ι ι C(X, ℂ))) :
    unitaryHom (sectionMatrixHom (X := X) (ι := ι)) v
      ∈ unitaryComponentOne (STW59.SectionAlgebra X ι) :=
  unitaryHom_mem_unitaryComponentOne _ hv

/-- **The direction the witness needs**: a pointwise null-homotopy over the base gives a
null-homotopy of the corresponding matrix of functions. -/
theorem sectionMatrixSymm_mem_unitaryComponentOne {v : unitary (STW59.SectionAlgebra X ι)}
    (hv : v ∈ unitaryComponentOne (STW59.SectionAlgebra X ι)) :
    unitaryHom (sectionMatrixSymmHom (X := X) (ι := ι)) v
      ∈ unitaryComponentOne (CStarMatrix ι ι C(X, ℂ)) :=
  unitaryHom_mem_unitaryComponentOne _ hv

end Transport

/-! ### Axiom audit -/

#audit_axioms sectionMatrixEquiv
#audit_axioms sectionMatrix_mem_unitaryComponentOne
#audit_axioms sectionMatrixSymm_mem_unitaryComponentOne

end

end LIX

end GroupApproximation
