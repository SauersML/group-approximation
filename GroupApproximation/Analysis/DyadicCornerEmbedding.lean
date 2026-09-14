import GroupApproximation.Analysis.MatrixUnitHom
import Mathlib.Data.Matrix.Basis

/-!
# Corner embeddings of matrix algebras

Infrastructure of lane `oa-hyperfinite` for "Brown's formulation" of `simple_kazhdan_sofic_group.tex`
(tex l.273–290 at 37551fd93).  The passage `∏_ω M_k → 𝓡^ω` sends `M_k` into the Pauli stage `M_{2^j}`
through `A ↦ A ⊗ 1_r` on a corner of size `k r ≤ 2^j`.  The corner is carried by an injection
`φ : Y × Fin r ↪ N`, and this module builds it without tensor products.

* `cornerUnit φ a b := Σ_{s<r} e_{φ(a,s), φ(b,s)}`, a system of matrix units
  (`cornerUnit_isMatrixUnits`).
* `trace_cornerUnit`: `trace (cornerUnit φ a b) = [a = b] r`, so
  `trace_cornerHom : trace (cornerHom φ A) = r · trace A`.
* `cornerHom φ`: the non-unital star homomorphism `Matrix Y Y ℂ →⋆ₙₐ[ℂ] Matrix N N ℂ`.
-/

namespace GroupApproximation
namespace MatrixUnits

open Matrix

noncomputable section

variable {Y N : Type*} [Fintype Y] [DecidableEq Y] [Fintype N] [DecidableEq N] {r : ℕ}

/-- **The corner matrix units** of an injection `φ : Y × Fin r ↪ N`. -/
def cornerUnit (φ : Y × Fin r ↪ N) (a b : Y) : Matrix N N ℂ :=
  ∑ s : Fin r, Matrix.single (φ (a, s)) (φ (b, s)) (1 : ℂ)

theorem cornerUnit_isMatrixUnits (φ : Y × Fin r ↪ N) : IsMatrixUnits (cornerUnit φ) where
  mul a b c d := by
    rw [cornerUnit, cornerUnit, Finset.sum_mul_sum]
    by_cases hbc : b = c
    · subst hbc
      rw [if_pos rfl, cornerUnit]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [Finset.sum_eq_single s]
      · rw [single_mul_single_same, mul_one]
      · intro t _ hts
        rw [single_mul_single_of_ne]
        intro h
        exact hts (congrArg Prod.snd (φ.injective h)).symm
      · intro h
        exact absurd (Finset.mem_univ s) h
    · rw [if_neg hbc]
      refine Finset.sum_eq_zero fun s _ ↦ Finset.sum_eq_zero fun t _ ↦ ?_
      rw [single_mul_single_of_ne]
      intro h
      exact hbc (congrArg Prod.fst (φ.injective h))
  star a b := by
    rw [cornerUnit, cornerUnit, star_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Matrix.star_eq_conjTranspose, conjTranspose_single, star_one]

theorem trace_cornerUnit (φ : Y × Fin r ↪ N) (a b : Y) :
    Matrix.trace (cornerUnit φ a b) = if a = b then (r : ℂ) else 0 := by
  rw [cornerUnit, Matrix.trace_sum]
  by_cases hab : a = b
  · subst hab
    simp only [trace_single_eq_same, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, if_true]
  · rw [if_neg hab]
    refine Finset.sum_eq_zero fun s _ ↦ ?_
    apply trace_single_eq_of_ne
    intro h
    exact hab (congrArg Prod.fst (φ.injective h))

/-- **The corner embedding** `A ↦ A ⊗ 1_r` on the corner of `φ`. -/
def cornerHom (φ : Y × Fin r ↪ N) : Matrix Y Y ℂ →⋆ₙₐ[ℂ] Matrix N N ℂ :=
  matrixUnitNonUnitalHom (cornerUnit_isMatrixUnits φ)

theorem cornerHom_apply (φ : Y × Fin r ↪ N) (M : Matrix Y Y ℂ) :
    cornerHom φ M = matrixUnitSum (cornerUnit φ) M :=
  rfl

/-- **The corner multiplies the trace by `r`.** -/
theorem trace_cornerHom (φ : Y × Fin r ↪ N) (M : Matrix Y Y ℂ) :
    Matrix.trace (cornerHom φ M) = (r : ℂ) * Matrix.trace M :=
  trace_matrixUnitSum (cornerUnit φ) (Matrix.traceLinearMap N ℂ ℂ) (r : ℂ)
    (trace_cornerUnit φ) M

/-- A corner exists as soon as `card Y · r ≤ card N`. -/
theorem nonempty_cornerEmbedding (h : Fintype.card Y * r ≤ Fintype.card N) :
    Nonempty (Y × Fin r ↪ N) :=
  Function.Embedding.nonempty_of_card_le (by rwa [Fintype.card_prod, Fintype.card_fin])

end

#audit_axioms cornerUnit_isMatrixUnits
#audit_axioms trace_cornerHom

end MatrixUnits
end GroupApproximation
