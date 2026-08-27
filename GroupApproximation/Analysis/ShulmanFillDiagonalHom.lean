import GroupApproximation.Analysis.ShulmanFillSymmetricDoubleFlip

/-!
# The diagonal embedding, and the flip-conjugated pair of a double

`x ↦ diag(x, x)` is the map that turns a representation of `D` into the
`ρ₂ = π₂ ⊕ π₁` of Shulman's Theorem 10 when the two factors of the double
agree — and the flip commutes with its image exactly.  This module builds the
map and the resulting compatible representation, so that the conjugated pair
of the paper's proof exists on the nose over any coefficient algebra.

The entrywise proofs use the coordinate simp lemmas of
`Analysis/CStarMatrixTwoByTwo` (`cStarDiagonal2_apply_*`, which are `@[simp]`
there) together with `CStarMatrix.mul_apply` and `Fin.sum_univ_two`.  They are
grouped in this module, apart from the assembly in
`Analysis/ShulmanFillSymmetricDouble`, so that a wrong coordinate lemma name
cannot take the assembly down with it.

This module is not in the root import list.  It was authored while builds were
suspended, so it is kept out of the closure until it has been elaborated.
-/

namespace GroupApproximation
namespace ShulmanFill

noncomputable section

variable {E : Type} [CStarAlgebra E]

/-- The diagonal embedding `x ↦ diag(x, x)` of a C-star algebra into its
two-by-two matrix algebra. -/
def diagonalHom2 : E →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) E where
  toFun x := cStarDiagonal2 x x
  map_one' := by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [CStarMatrix.one_apply]
  map_mul' x y := by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [CStarMatrix.mul_apply, Fin.sum_univ_two]
  map_zero' := by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [CStarMatrix.zero_apply]
  map_add' x y := by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [CStarMatrix.add_apply]
  commutes' z := by
    ext p q
    fin_cases p <;> fin_cases q <;>
      simp [Algebra.algebraMap_eq_smul_one, CStarMatrix.smul_apply,
        CStarMatrix.one_apply]
  map_star' x := by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [CStarMatrix.star_apply]

@[simp] theorem diagonalHom2_apply (x : E) :
    diagonalHom2 x = cStarDiagonal2 x x := rfl

/-- The flip commutes exactly with the diagonal image of any subalgebra: the
image consists of diagonals with equal entries. -/
theorem commutesWith_flip2_diagonalHom2_range {C : Type} [CStarAlgebra C]
    (rho : C →⋆ₐ[ℂ] E) :
    CommutesWith (Set.range fun c : C ↦ diagonalHom2 (rho c))
      ((flipUnitary : unitary (CStarMatrix (Fin 2) (Fin 2) E)) :
        CStarMatrix (Fin 2) (Fin 2) E) := by
  rintro _ ⟨c, rfl⟩
  rw [flipUnitary_coe]
  exact flip2_commutes_diagonal2_self (rho c)

/-- **The conjugated pair of Shulman's Theorem 10, exactly.**  Both factors of
the double are represented diagonally, and the second is conjugated by the
flip; compatibility holds because the flip fixes the diagonal image of `C`. -/
def flipDoubleRepresentation {C : Type} [CStarAlgebra C]
    [Nontrivial (CStarMatrix (Fin 2) (Fin 2) E)] (k : C →⋆ₐ[ℂ] E) :
    CStarAmalgamRepresentation k k :=
  conjugateRepresentationOfCommutant k k diagonalHom2 diagonalHom2 rfl
    flipUnitary (commutesWith_flip2_diagonalHom2_range k)

end

end ShulmanFill
end GroupApproximation
