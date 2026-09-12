import GroupApproximation.Analysis.LIXLemmaSixGenerator

/-!
# The shape of the generator along the tower

The manuscript's Lemma 6 joins `v_i = φ_{0,i}(u)` to `w_i = u ⊕ 1_{H_i}` by a
path, and the path exists because the extra block is a unitary of a full
matrix algebra.  That argument needs the unitary group of `Matrix (Fin r) (Fin
r) ℂ` to be path connected, which is **not** in Mathlib at pin `81a5d257`
(`Analysis/Matrix/Spectrum.lean` has only the Hermitian spectral theorem, and
`LinearAlgebra/Matrix/UnitaryGroup.lean` has no connectedness result).

It is also not needed.  Every block that `STW59.connect` adds is constant in
the `S⁴` coordinate: `connectMatrix i M` has new block
`constMat (compressMat i M) ⊗ₖ newLine i`, where `compressMat` reads `M` only
at the fixed point `stagePoint i` and `newLine i` is pulled back from the
newest projective factor (`STW59.newLine_eq_pullMat`).  So

    lixTower.climb j 0 genStage  =  u ⊕ c_j

is an **equality**, with `c_j` a matrix over `Y_j` alone, and the generalised
Corollary 4 — which quantifies over all such `c` — applies to it directly.
No homotopy appears anywhere, and Lemma 6 disappears.

This file carries the first half: the generator read at every stage
(`genMatAt`), its compatibility with the base projections, and the shape
predicate with its base case.
-/

namespace GroupApproximation
namespace LIX

open scoped Matrix ComplexOrder CStarAlgebra

set_option linter.unusedSectionVars false

noncomputable section

/-! ## The generator read at an arbitrary stage

`genMat` is the generator over `X₀`.  Because `basePr` and `baseProj` are the
identity on the `S⁴` coordinate, pulling it back to `X_j` gives the matrix
with the same formula, which is what makes the induction below an equality of
matrices rather than a chain of pullbacks. -/

theorem continuous_genMatFunAt (j : ℕ) :
    Continuous fun w : STW59.baseX j =>
      genU2 (equatorEmb (w.1 : EuclideanSpace ℝ (Fin 5))) :=
  continuous_genU2
    (continuous_equatorEmb.comp (continuous_subtype_val.comp continuous_fst))
    (fun w => equatorEmb_mem w.1.2)
    (fun _ => equatorEmb_ne_neg_one _)
    (fun _ => equatorEmb_ne_one _)

/-- The generator as a `2 × 2` matrix of continuous functions on `X_j`. -/
def genMatAt (j : ℕ) : Matrix (Fin 2) (Fin 2) C(STW59.baseX j, ℂ) :=
  Matrix.of fun i k =>
    ⟨fun w => genU2 (equatorEmb (w.1 : EuclideanSpace ℝ (Fin 5))) i k,
      (continuous_genMatFunAt j).matrix_elem i k⟩

@[simp]
theorem matEval_genMatAt (j : ℕ) (w : STW59.baseX j) :
    STW59.matEval w (genMatAt j) = genU2 (equatorEmb (w.1 : EuclideanSpace ℝ (Fin 5))) := rfl

theorem genMatAt_zero : genMatAt 0 = genMat := rfl

/-- Pulling the generator back along any base projection leaves it unchanged,
because the projections are the identity on the `S⁴` coordinate. -/
theorem pullMat_basePr_genMatAt {k j : ℕ} (h : k ≤ j) :
    STW59.pullMat (STW59.basePr h) (genMatAt k) = genMatAt j := by
  refine STW59.matrix_ext_of_matEval fun w => ?_
  rw [STW59.matEval_pullMat, matEval_genMatAt, matEval_genMatAt, STW59.basePr_apply]

theorem pullMat_baseProj_genMatAt (j : ℕ) :
    STW59.pullMat (STW59.baseProj j) (genMatAt j) = genMatAt (j + 1) := by
  refine STW59.matrix_ext_of_matEval fun w => ?_
  rw [STW59.matEval_pullMat, matEval_genMatAt, matEval_genMatAt]
  rfl

/-! ## The shape predicate -/

/-- **`a` has the generator shape at stage `j`**: its `𝟏²` block is the
generator, which depends only on the `S⁴` coordinate, and its `H` block is
pulled back from `Y_j`, so it does not depend on `S⁴` at all.

This is the honest content of the manuscript's Lemma 6.  Corollary 4 is
proved for every element of this shape, and the shape is preserved by
`connect`, so the composite `φ_{0,j}` never leaves it. -/
def HasGeneratorShape (j : ℕ) (a : STW59.StageAlgebra j) : Prop :=
  ∃ c : Matrix (STW59.HIdx j) (STW59.HIdx j) C(STW59.baseY j, ℂ),
    STW59.toFunctionMatrix (a : STW59.SectionAlgebra (STW59.baseX j) (STW59.EIdx j))
      = Matrix.fromBlocks (genMatAt j) 0 0 (STW59.pullMat (STW59.baseYproj j) c)

/-- At stage zero the `H` block is empty, so the generator itself has the
shape. -/
theorem hasGeneratorShape_zero : HasGeneratorShape 0 genStage := by
  refine ⟨0, ?_⟩
  rw [coe_genStage, STW59.toFunctionMatrix_ofFunctionMatrix, STW59.blockUnitary_def,
    STW59.Hproj_zero, STW59.pullMat_zero, genMatAt_zero]

end

end LIX
end GroupApproximation
