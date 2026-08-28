import GroupApproximation.Analysis.CStarMatrixTwoByTwo
import GroupApproximation.Analysis.ShulmanFillCommutantExact

/-!
# The flip of Shulman's Theorem 10, and what still stands between it and the
symmetric double

`ShulmanSymmetricDouble.SymmetricDoubleMFStatement` is Shulman's Theorem 10.
Its proof turns on one exact identity, and this module supplies it.

With `π = π₁ * π₂ : D *_C D → B(H)` faithful, put `ρ₁ = π₁ ⊕ π₂` and
`ρ₂ = π₂ ⊕ π₁` inside `M₂(B(H))`.  The two are conjugate by the flip
`u = ((0,1),(1,0))`, and on the amalgamated algebra they are *equal*: since
`π₁|_C = π₂|_C`, the element `ρ₂(c)` is the diagonal `cStarDiagonal2 (π₁ c)
(π₁ c)`, and the flip commutes with every such diagonal exactly.  That is
`flip2_commutes_diagonal2_self` below, and it is the whole reason Theorem 10
needs no genericity estimate: the decoupling unitary is explicit, and only its
*lift* to the matrix models is approximate.

## What is proved here

* `flip2`, its self-adjointness, `flip2 * flip2 = 1`, and `flipUnitary`;
* `flip2_conj_diagonal2` — conjugation by the flip swaps the two diagonal
  entries, which is `ρ₁ = u* ρ₂ u`;
* `flip2_commutes_diagonal2_self` and `commutesWith_flip2_diagonalRange` —
  the exact commutation with the diagonal image of `C`, in the vocabulary of
  `ShulmanFill.CommutesWith`, so that `conjugateRepresentationOfCommutant`
  accepts it directly.

## What still stands between this and `SymmetricDoubleMFStatement`

Three inputs of the paper, none of them an estimate about generic position:

1. **Theorem 4** (Shulman, arXiv:2603.13564v2 p. 5, quoted there from [27,
   Th. 14]): for separable `A`, `A` is MF iff every `*`-homomorphism
   `A → B(H)` lifts to a discrete asymptotic homomorphism `A → 𝒟`, where
   `𝒟 ⊂ ∏ₙ Mₙ` is the algebra of `*`-strongly convergent matrix sequences and
   `q : 𝒟 → B(H)` sends a sequence to its `*`-strong limit.  Remark 6 makes
   the lift contractive.  **The repository has no `𝒟`**: it has the bounded
   product `BoundedMatrixSequence` and the norm quotient by null sequences,
   but not the `*`-strongly convergent subalgebra nor the limit map.  Building
   `𝒟` and `q` is a construction task, not an estimate, and it is the first
   thing this route needs.
2. **Lemma 9** (p. 6–7): the Halmos dilation.  Lift `u` to a contraction `X`,
   correct it by a quasicentral approximate unit to `X̃ = X(1 - i_λ)`
   (Lemma 8), and set `V = ((X̃, √(1 - X̃X̃*)), (√(1 - X̃*X̃), -X̃*))`; Pedersen's
   inequality `‖[A^{1/2}, B]‖ ≤ (5/4)‖[A, B]‖^{1/2}` controls the square-root
   corners, giving `‖[V, diag(Aᵢ, Aᵢ)]‖ ≤ ε`.  This is what
   `Analysis/ShulmanHalmosDilation*`, `Analysis/ShulmanCoronaHalmos*` and
   `Analysis/ShulmanCoronaSquareRoot*` are for.
3. **Lemma 7** (p. 5–6): two contractive asymptotic homomorphisms agreeing
   asymptotically on `C` glue to one on the amalgam, via a contractive section
   of `C_b(Λ, D) → C_b(Λ, D)/C_0(Λ, D)`.  The corona-valued special case is
   `MFAlgebraAmalgamCriterion.exists_compatible_asymptotic_amalgam_model`.

Given 1–3, Theorem 10 is: lift `ρ₂` (Theorem 4 + Remark 6), dilate `u ⊕ -u*`
(Lemma 9) to `V_k` with `‖[V_k, φ_k(c) ⊕ φ_k(c)]‖ ≤ 1/k` on the `k`-th
initial segment of a dense sequence of `C`, set `φ⁽¹⁾_k = V_k* φ⁽²⁾_k V_k`,
check asymptotic agreement on `C` (the estimate on p. 8, whose shape is
`ShulmanDenseCompatibility.tendsto_norm_sub_of_dense`), glue by Lemma 7, and
conclude by Theorem 4 again.

`Analysis/ShulmanFillFlipUnitary` carried a second `ShulmanFill.flipUnitary`,
with `flip`/`coe_flipUnitary`/`flip_mul_diagonal2_mul_flip`/
`flip_commute_diagonal2` in place of `flip2`/`flipUnitary_coe`/
`flip2_conj_diagonal2`/`flip2_commutes_diagonal2_self` here.  Nothing imported
it and every one of its declarations has a counterpart above, so it was retired
rather than wired: two modules declaring `GroupApproximation.ShulmanFill.
flipUnitary` cannot both be in one import closure.

This module is in the root import list.  It was authored while builds were
suspended and has not been elaborated.  The entrywise proofs below all use one
idiom — `ext`, `fin_cases`, `simp` with the `CStarMatrix` coordinate lemmas —
copied from `Analysis/CStarMatrixTwoByTwo`; if a coordinate simp lemma is named
differently they fail together and are fixed together.
-/

namespace GroupApproximation
namespace ShulmanFill

noncomputable section

variable {E : Type} [CStarAlgebra E]

/-- The two-by-two matrices over a C-star algebra form a C-star algebra.
Mathlib assembles this out of the positivity order of `E`, so `PartialOrder E`
and `StarOrderedRing E` have to be available while the instance is built.  They
are introduced by `letI` *inside this proof* rather than as ambient instances:
as ambient instances they enter the `Semiring`/`StarRing` paths of `E` itself
and make later goals ill-typed at `instances` transparency.  This mirrors
`MFRecognition.HNNPermanenceUedaOperations.matrixTwoCStarAlgebra`, which is not
in this module's import closure. -/
noncomputable instance flipMatrixTwoCStarAlgebra :
    CStarAlgebra (CStarMatrix (Fin 2) (Fin 2) E) := by
  letI : PartialOrder E := CStarAlgebra.spectralOrder E
  letI : StarOrderedRing E := CStarAlgebra.spectralOrderedRing E
  exact inferInstance

/-! ## The flip -/

/-- The flip `((0,1),(1,0))` of a two-by-two C-star matrix algebra. -/
def flip2 : CStarMatrix (Fin 2) (Fin 2) E :=
  cStarMatrixUnit2 0 1 + cStarMatrixUnit2 1 0

@[simp] theorem star_flip2 :
    star (flip2 : CStarMatrix (Fin 2) (Fin 2) E) = flip2 := by
  show star (cStarMatrixUnit2 (A := E) 0 1 + cStarMatrixUnit2 (A := E) 1 0)
    = cStarMatrixUnit2 (A := E) 0 1 + cStarMatrixUnit2 (A := E) 1 0
  rw [star_add, cStarMatrixUnit2_star, cStarMatrixUnit2_star, add_comm]

theorem flip2_mul_flip2 :
    (flip2 : CStarMatrix (Fin 2) (Fin 2) E) * flip2 = 1 := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [flip2, cStarMatrixUnit2, CStarMatrix.mul_apply, Matrix.single_apply]

/-- The flip, as a unitary. -/
def flipUnitary : unitary (CStarMatrix (Fin 2) (Fin 2) E) :=
  ⟨flip2, by
    constructor
    · rw [star_flip2, flip2_mul_flip2]
    · rw [star_flip2, flip2_mul_flip2]⟩

@[simp] theorem flipUnitary_coe :
    ((flipUnitary : unitary (CStarMatrix (Fin 2) (Fin 2) E)) :
      CStarMatrix (Fin 2) (Fin 2) E) = flip2 := rfl

/-! ## Conjugation by the flip swaps the two summands -/

/-- `u* diag(x, y) u = diag(y, x)`: this is `ρ₁ = u* ρ₂ u` of the paper. -/
theorem flip2_conj_diagonal2 (x y : E) :
    (flip2 : CStarMatrix (Fin 2) (Fin 2) E) * cStarDiagonal2 x y * flip2 =
      cStarDiagonal2 y x := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [flip2, cStarMatrixUnit2, cStarDiagonal2, CStarMatrix.mul_apply,
      Matrix.single_apply, Matrix.diagonal_apply]

theorem unitaryConj_flipUnitary_diagonal2 (x y : E) :
    unitaryConj (flipUnitary : unitary (CStarMatrix (Fin 2) (Fin 2) E))
        (cStarDiagonal2 x y) = cStarDiagonal2 y x := by
  show (flip2 : CStarMatrix (Fin 2) (Fin 2) E) * cStarDiagonal2 x y *
    star (flip2 : CStarMatrix (Fin 2) (Fin 2) E) = cStarDiagonal2 y x
  rw [star_flip2, flip2_conj_diagonal2]

/-! ## Exact commutation with the amalgamated part -/

/-- **The identity Theorem 10 turns on.**  The flip commutes exactly with a
diagonal whose two entries agree — and the image of the amalgamated algebra is
exactly such a diagonal, because the two factor representations of a double
agree on `C`. -/
theorem flip2_commutes_diagonal2_self (x : E) :
    (flip2 : CStarMatrix (Fin 2) (Fin 2) E) * cStarDiagonal2 x x =
      cStarDiagonal2 x x * flip2 := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [flip2, cStarMatrixUnit2, cStarDiagonal2, CStarMatrix.mul_apply,
      Matrix.single_apply, Matrix.diagonal_apply]

/-- The flip lies in the commutant of the diagonal image of `C`, in the form
`ShulmanFill.conjugateRepresentationOfCommutant` consumes. -/
theorem commutesWith_flip2_diagonalRange {C : Type} [CStarAlgebra C]
    (rho : C →⋆ₐ[ℂ] E) :
    CommutesWith (Set.range fun c : C ↦ cStarDiagonal2 (rho c) (rho c))
      ((flipUnitary : unitary (CStarMatrix (Fin 2) (Fin 2) E)) :
        CStarMatrix (Fin 2) (Fin 2) E) := by
  rintro _ ⟨c, rfl⟩
  rw [flipUnitary_coe]
  exact flip2_commutes_diagonal2_self (rho c)

/-- Conjugation by the flip is the identity on the diagonal image of `C`.
This is the exact statement that the two asymptotic homomorphisms of the
paper's proof agree on `C` *before* any approximation is made. -/
theorem unitaryConj_flipUnitary_eq_self_on_diagonalRange {C : Type}
    [CStarAlgebra C] (rho : C →⋆ₐ[ℂ] E) (c : C) :
    unitaryConj (flipUnitary : unitary (CStarMatrix (Fin 2) (Fin 2) E))
        (cStarDiagonal2 (rho c) (rho c)) = cStarDiagonal2 (rho c) (rho c) :=
  unitaryConj_flipUnitary_diagonal2 (rho c) (rho c)

end

end ShulmanFill
end GroupApproximation
