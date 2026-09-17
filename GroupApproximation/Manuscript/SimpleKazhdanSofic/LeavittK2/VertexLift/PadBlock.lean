import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.VertexStab
import GroupApproximation.Algebra.ElementaryPaddingInjective
import GroupApproximation.Meta.AxiomGuard

/-!
# The block factorization `j(b, H) = [[H, 0], [0, 1]] · [[1, 0], [b, 1]]` (lane sk-leavitt-05)

Khanh (arXiv:2609.08428), proof of Theorem 5.1.  For `g ∈ J` with blocks `H = upperBlock g` and
`b = bottomRow g`, the padding `padHom castSuccEmb H = [[H, 0], [0, 1]]` times
`rowMat b = [[1, 0], [b, 1]]` is `[[H, 0], [b, 1]] = g` (`padHom_mul_rowMat`).  This is the
matrix identity behind `projection (ℓ(H) · x_last(b)) = g`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift

open scoped Matrix

local notation "𝓛" => GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)

theorem padEquiv_symm_castSucc (i : Fin 3) :
    (ElementaryPadding.padEquiv (Fin.castSuccEmb (n := 3))).symm i.castSucc = Sum.inl i :=
  (Equiv.symm_apply_eq _).mpr rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.padEquiv_symm_castSucc

theorem last_not_mem_range_castSuccEmb : Fin.last 3 ∉ Set.range (Fin.castSuccEmb (n := 3)) := by
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i hi

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.last_not_mem_range_castSuccEmb

theorem padEquiv_symm_last :
    (ElementaryPadding.padEquiv (Fin.castSuccEmb (n := 3))).symm (Fin.last 3) =
      Sum.inr ⟨Fin.last 3, last_not_mem_range_castSuccEmb⟩ :=
  (Equiv.symm_apply_eq _).mpr rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.padEquiv_symm_last

theorem pad_cs_cs (M : Matrix (Fin 3) (Fin 3) 𝓛) (i j : Fin 3) :
    ElementaryPadding.padHom (Fin.castSuccEmb (n := 3)) M i.castSucc j.castSucc = M i j :=
  ElementaryPadding.padHom_apply_embed Fin.castSuccEmb M i j

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.pad_cs_cs

theorem pad_cs_last (M : Matrix (Fin 3) (Fin 3) 𝓛) (i : Fin 3) :
    ElementaryPadding.padHom (Fin.castSuccEmb (n := 3)) M i.castSucc (Fin.last 3) = 0 := by
  rw [ElementaryPadding.padHom_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    padEquiv_symm_castSucc, padEquiv_symm_last, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.pad_cs_last

theorem pad_last_cs (M : Matrix (Fin 3) (Fin 3) 𝓛) (j : Fin 3) :
    ElementaryPadding.padHom (Fin.castSuccEmb (n := 3)) M (Fin.last 3) j.castSucc = 0 := by
  rw [ElementaryPadding.padHom_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    padEquiv_symm_castSucc, padEquiv_symm_last, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.pad_last_cs

theorem pad_last_last (M : Matrix (Fin 3) (Fin 3) 𝓛) :
    ElementaryPadding.padHom (Fin.castSuccEmb (n := 3)) M (Fin.last 3) (Fin.last 3) = 1 := by
  rw [ElementaryPadding.padHom_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    padEquiv_symm_last, Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.pad_last_last

/-- **`[[H, 0], [0, 1]] · [[1, 0], [b, 1]] = [[H, 0], [b, 1]]`** for `g = j(b, H) ∈ J`. -/
theorem padHom_mul_rowMat (g : Criterion.vertexStab) :
    ElementaryPadding.padHom (Fin.castSuccEmb (n := 3)) (upperBlock g) * rowMat (bottomRow g) =
      mat g := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [rowMat_castSucc]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · simp only [pad_cs_cs, pad_cs_last, zero_mul, add_zero, one_castSucc_castSucc]
      have h1 := congrFun (congrFun (Matrix.mul_one (upperBlock g)) i) j
      rw [Matrix.mul_apply] at h1
      rw [h1, upperBlock_apply]
    · simp only [one_castSucc_last, mul_zero, Finset.sum_const_zero, pad_cs_last, zero_mul,
        add_zero]
      exact (mat_castSucc_last g i).symm
  · simp only [pad_last_cs, zero_mul, Finset.sum_const_zero, zero_add, pad_last_last, one_mul]
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · rw [rowMat_last_castSucc, bottomRow_apply]
    · rw [rowMat_last_last, mat_last_last]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift.padHom_mul_rowMat

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.VertexLift
