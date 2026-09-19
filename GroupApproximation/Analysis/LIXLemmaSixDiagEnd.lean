import GroupApproximation.Analysis.LIXLemmaSixDiag

/-!
# `hdiag`: the transported homotopy is exactly `diag(u, 1)`

`Analysis/LIXLemmaSixDiag.lean` carries the null-homotopy of `genU ⊕ 1` along
the chain into `M₂(A₀)`.  What is left, and what this file does, is to identify
the transported unitary with `diagOne genUnitary` on the nose.

That identification is where the block-diagonality of `genU` is spent for the
last time.  `finProdFinEquiv` sends `(i, k)` to `k + 2 i`, so the first
`M₂`-block of a `4 × 4` matrix is rows and columns `{0, 1}` and the second is
`{2, 3}`.  Under `paddedPath4 0`, which is `genU ⊕ 1` in the `3 + 1` splitting,
the first block is therefore the top-left `2 × 2` of `genU`, which is `genU2`;
the second is `diag (genU 2 2, 1)`, which is `1` because `genU` fixes `e₃`; and
the off-diagonal blocks vanish for the same reason.  That is precisely the
entry pattern of `diagOne`.
-/

namespace GroupApproximation
namespace LIX

open scoped Matrix ComplexOrder CStarAlgebra

attribute [local instance 100000] GroupApproximation.LIX.instSpectralPartialOrder
                                  GroupApproximation.LIX.instSpectralStarOrderedRing

set_option linter.unusedSectionVars false
-- `simp` below runs under `<;>` over sixteen branches and uses different
-- arguments in different ones; the unusedSimpArgs linter aggregates and
-- reports them as unused, but removing any of them leaves goals open.
set_option linter.unusedSimpArgs false

noncomputable section

/-! ## `genU` is block-diagonal, entrywise

`genU_mul_rk1` and `rk1_e3_mul_genU` say that `genU` fixes the pole; read at a
single entry they give the third row and the third column outright. -/

theorem genU_apply_two_right {x : Fin 3 → ℂ} (hx : x ∈ STW59.unitVectors (Fin 3))
    (hN : x 2 ≠ -1) (hS : x 2 ≠ 1) (i : Fin 3) : genU x i 2 = e3 i := by
  have h := congrFun₂ (genU_mul_rk1 hx hN hS e3) i 2
  simpa [Matrix.mul_apply, rk1_apply, e3, Fin.sum_univ_three, Pi.single_apply] using h

theorem genU_apply_two_left {x : Fin 3 → ℂ} (hx : x ∈ STW59.unitVectors (Fin 3))
    (hN : x 2 ≠ -1) (hS : x 2 ≠ 1) (j : Fin 3) : genU x 2 j = e3 j := by
  have h := congrFun₂ (rk1_e3_mul_genU hx hN hS) 2 j
  simpa [Matrix.mul_apply, rk1_apply, e3, Fin.sum_univ_three, Pi.single_apply] using h

/-! ## The entries of the homotopy at time zero -/

theorem paddedPath_zero_apply (a : EuclideanSpace ℝ (Fin 5)) (i j : Fin 3 ⊕ Fin 1) :
    paddedPath 0 a i j
      = Matrix.fromBlocks (genU (equatorEmb a)) 0 0 1 i j := by
  rw [paddedPath_zero]

/-- The top-left `2 × 2` block of `genU` is `genU2`. -/
theorem genU2_apply (x : Fin 3 → ℂ) (a b : Fin 2) :
    genU2 x a b = genU x (Fin.castSucc a) (Fin.castSucc b) := by
  simp only [genU2, incl, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> norm_num

/-- The composite index map: `finProdFinEquiv` puts block `i` at
`{2i, 2i+1}`, and `finSumFinEquiv.symm` splits `Fin 4` as `Fin 3 ⊕ Fin 1`. -/
theorem symm_finTwoTwo (i a : Fin 2) :
    (@finSumFinEquiv 3 1).symm (finTwoTwo (i, a))
      = if i = 0 then Sum.inl (Fin.castSucc a)
        else if a = 0 then Sum.inl 2 else Sum.inr 0 := by
  fin_cases i <;> fin_cases a <;> rfl

/-! ## The transported unitary, entrywise

Every arrow of `diagChain` is a rearrangement of indices, so the composite is
definitional and a single `rfl` reads off the entry. -/

theorem transported_entry (i j : Fin 2) (w : STW59.baseX 0) (a b : Fin 2) :
    ((unitaryHom diagChain (unitaryHom sectionMatrixSymmHom (paddedUnitary 0)) :
        CStarMat 2 (STW59.StageAlgebra 0)) i j :
        STW59.SectionAlgebra (STW59.baseX 0) (STW59.EIdx 0)) w (Sum.inl a) (Sum.inl b)
      = paddedPath4 0 ((w.1 : ↥STW59.sphereFour) : EuclideanSpace ℝ (Fin 5))
          (finTwoTwo (i, a)) (finTwoTwo (j, b)) := rfl

/-- The entries of `diagOne genUnitary`, read in the same coordinates. -/
theorem diagOne_genUnitary_entry (i j : Fin 2) (w : STW59.baseX 0) (a b : Fin 2) :
    ((diagOne genUnitary : CStarMat 2 (STW59.StageAlgebra 0)) i j :
        STW59.SectionAlgebra (STW59.baseX 0) (STW59.EIdx 0)) w (Sum.inl a) (Sum.inl b)
      = if (i : ℕ) = 0 then
          (if (j : ℕ) = 0 then
            genU2 (equatorEmb ((w.1 : ↥STW59.sphereFour) : EuclideanSpace ℝ (Fin 5))) a b
           else 0)
        else (if (j : ℕ) = 0 then 0 else if a = b then 1 else 0) := by
  rw [coe_diagOne_apply]
  by_cases hi : (i : ℕ) = 0 <;> by_cases hj : (j : ℕ) = 0 <;>
    simp [hi, hj, coe_genUnitary, coe_genStage, STW59.blockUnitary_def,
      STW59.coe_stageAlgebra_one, STW59.stageProj, Eproj_zero_eq_one, Matrix.one_apply,
      genMat, apply_ite (fun f : C(STW59.baseX 0, ℂ) => f w)]

/-- **`hdiag`.**  The transported unitary is `diag(u, 1)` on the nose, so the
null-homotopy of `paddedPath` is a null-homotopy of `diagOne genUnitary`. -/
theorem transported_eq_diagOne :
    unitaryHom diagChain (unitaryHom sectionMatrixSymmHom (paddedUnitary 0))
      = diagOne genUnitary := by
  refine Subtype.ext (CStarMatrix.ext fun i j => ?_)
  refine STW59.corner_ext (ContinuousMap.ext fun w => ?_)
  refine Matrix.ext fun a b => ?_
  rcases a with a | a
  swap
  · exact a.elim
  rcases b with b | b
  swap
  · exact b.elim
  have hmem : equatorEmb ((w.1 : ↥STW59.sphereFour) : EuclideanSpace ℝ (Fin 5))
      ∈ STW59.unitVectors (Fin 3) := equatorEmb_mem w.1.2
  have hN : equatorEmb ((w.1 : ↥STW59.sphereFour) : EuclideanSpace ℝ (Fin 5)) 2 ≠ -1 :=
    equatorEmb_ne_neg_one _
  have hS : equatorEmb ((w.1 : ↥STW59.sphereFour) : EuclideanSpace ℝ (Fin 5)) 2 ≠ 1 :=
    equatorEmb_ne_one _
  rw [transported_entry, diagOne_genUnitary_entry, paddedPath4, Matrix.reindex_apply,
    Matrix.submatrix_apply, paddedPath_zero, symm_finTwoTwo, symm_finTwoTwo]
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [genU2_apply, genU_apply_two_left hmem hN hS, genU_apply_two_right hmem hN hS,
      e3, Pi.single_apply]

/-- **The second hypothesis of `lixLimit_hasK1InjWitness`.** -/
theorem hdiag_genUnitary :
    diagOne genUnitary ∈ unitaryComponentOne (CStarMat 2 (STW59.StageAlgebra 0)) := by
  have h := transported_mem
  rwa [transported_eq_diagOne] at h

end

end LIX
end GroupApproximation
