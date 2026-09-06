import GroupApproximation.Analysis.LIXLemmaSixShape
import GroupApproximation.Analysis.LIXLimitAlgebra

/-!
# The generator keeps its shape all the way up the tower

`Analysis/LIXLemmaSixShape.lean` defines `HasGeneratorShape` and checks it at
stage zero.  This file supplies the induction: `STW59.connect` preserves the
shape, so `lixTower.climb j 0 genStage` has it at every stage.

The step is where the manuscript's Lemma 6 is replaced by an equality.  The
new block of `connectMatrix j M` is
`constMat (compressMat j M) ⊗ₖ newLine j`, and both factors are constant in
the `S⁴` coordinate: `compressMat` reads `M` only at the fixed point
`stagePoint j`, and `newLine j` is pulled back from `Y_{j+1}`
(`STW59.newLine_eq_pullMat`).  The old blocks are pulled back along
`baseProj j`, which is the identity on `S⁴`
(`pullMat_baseProj_genMatAt`) and factors through `Y_j` on the rest
(`STW59.baseYproj_comp_baseProj`).  So the shape is reproduced verbatim one
level up, with no homotopy and no appeal to connectedness of a unitary group.
-/

namespace GroupApproximation
namespace LIX

open scoped Matrix Kronecker ComplexOrder CStarAlgebra

set_option linter.unusedSectionVars false

noncomputable section

/-- Associativity of the block sum under the reindexing `eIdxSucc`, in the
form `STW59.Eproj_succ` uses it: entrywise it is `rfl`. -/
theorem reindex_eIdxSucc_fromBlocks {j : ℕ}
    (P : Matrix (Fin 2) (Fin 2) C(STW59.baseX (j + 1), ℂ))
    (Q : Matrix (STW59.HIdx j) (STW59.HIdx j) C(STW59.baseX (j + 1), ℂ))
    (N : Matrix (STW59.NIdx j) (STW59.NIdx j) C(STW59.baseX (j + 1), ℂ)) :
    Matrix.reindex (STW59.eIdxSucc j) (STW59.eIdxSucc j)
        (Matrix.fromBlocks (Matrix.fromBlocks P 0 0 Q) 0 0 N)
      = Matrix.fromBlocks P 0 0 (Matrix.fromBlocks Q 0 0 N) := by
  ext a b
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;> rfl

theorem toFunctionMatrix_connect (j : ℕ) (a : STW59.StageAlgebra j) :
    STW59.toFunctionMatrix
        ((STW59.connect j a : STW59.StageAlgebra (j + 1)) :
          STW59.SectionAlgebra (STW59.baseX (j + 1)) (STW59.EIdx (j + 1)))
      = STW59.connectMatrix j
          (STW59.toFunctionMatrix
            (a : STW59.SectionAlgebra (STW59.baseX j) (STW59.EIdx j))) := rfl

/-- **The connecting map preserves the generator shape.**  This is the
manuscript's Lemma 6, as an equality rather than a homotopy. -/
theorem hasGeneratorShape_connect {j : ℕ} {a : STW59.StageAlgebra j}
    (h : HasGeneratorShape j a) : HasGeneratorShape (j + 1) (STW59.connect j a) := by
  obtain ⟨c, hc⟩ := h
  show ∃ _, _
  rw [toFunctionMatrix_connect, STW59.connectMatrix]
  generalize STW59.compressMat j
      (STW59.toFunctionMatrix (a : STW59.SectionAlgebra (STW59.baseX j) (STW59.EIdx j))) = N
  refine ⟨Matrix.fromBlocks (STW59.pullMat (STW59.baseYtrunc j) c) 0 0
      (STW59.constMat (STW59.baseY (j + 1)) N ⊗ₖ STW59.newLineY j), ?_⟩
  have hinner :
      Matrix.fromBlocks
          (STW59.pullMat (STW59.baseYproj (j + 1)) (STW59.pullMat (STW59.baseYtrunc j) c)) 0 0
          (STW59.pullMat (STW59.baseYproj (j + 1))
            (STW59.constMat (STW59.baseY (j + 1)) N ⊗ₖ STW59.newLineY j))
        = STW59.pullMat (STW59.baseYproj (j + 1))
            (Matrix.fromBlocks (STW59.pullMat (STW59.baseYtrunc j) c) 0 0
              (STW59.constMat (STW59.baseY (j + 1)) N ⊗ₖ STW59.newLineY j)) := by
    rw [STW59.pullMat_fromBlocks, STW59.pullMat_zero, STW59.pullMat_zero]
  rw [hc, STW59.pullMat_fromBlocks, STW59.pullMat_zero, STW59.pullMat_zero,
    pullMat_baseProj_genMatAt, STW59.pullMat_comp, STW59.baseYproj_comp_baseProj,
    ← STW59.pullMat_comp, STW59.newLine_eq_pullMat,
    ← STW59.pullMat_constMat (STW59.baseYproj (j + 1)) N, ← STW59.pullMat_kronecker,
    reindex_eIdxSucc_fromBlocks, hinner]
  rfl

/-- **The generator has the shape at every stage.**  Stated at
`lixTower.climb j 0`, the tower's own iterated map, so that
`CStarTower.climbHom_apply` makes the join with `cs-endpoint`'s `hstage`
definitional. -/
theorem hasGeneratorShape_climb (j : ℕ) :
    HasGeneratorShape j (lixTower.climb j 0 genStage) := by
  induction j with
  | zero =>
      rw [CStarTower.climb_self]
      exact hasGeneratorShape_zero
  | succ i ih =>
      rw [lixTower.climb_succ (Nat.zero_le i), lixTower_succHom]
      exact hasGeneratorShape_connect ih

end

end LIX
end GroupApproximation
