import GroupApproximation.Analysis.LIXLemmaSixField
import GroupApproximation.Analysis.LIXLemmaSixHIdx
import GroupApproximation.Analysis.LIXLemmaSixClimb
import GroupApproximation.Analysis.LIXLemmaSixCompare
import GroupApproximation.Analysis.LIXLemmaSixDiagEnd

/-!
# Corollary 4, and the endpoint

The generator `u` of `Analysis/LIXLemmaSixGenerator.lean` climbs the tower with the shape
`u ⊕ c_j` (`Analysis/LIXLemmaSixShape.lean`), the null-homotopy of such an element would
produce a continuous unitary field over `S⁵ × Y_j`
(`Analysis/LIXLemmaSixField.lean`), and such a field is the Murray--von Neumann equivalence
Lemma 2 denies (`Analysis/LIXLemmaSixCompare.lean`).  This file runs that argument:
`climb_genUnitary_notMem` is **Corollary 4**, and `lixLimit_hasK1InjWitness_of` is the
endpoint the C⋆-side consumes, conditional on the single topological input
`LIX.LemmaTwoHolds`.

The only work here is bookkeeping between two presentations of the same data: the
homotopy is a path in the corner `E_j · M_{E_j}(C(X_j)) · E_j`, indexed by
`STW59.EIdx j = Fin 2 ⊕ STW59.HIdx j`, and the field has to be indexed by the
manuscript's `Fin 2 ⊕ CharClass.HIdx (lixDD j)`.  `Analysis/LIXLemmaSixHIdx.lean` supplies
the reindexing and the identification of the two `H`-projections; everything below is its
transport.

## Main results

* `false_of_path` — the argument, from an abstract path in the stage algebra.
* `climb_genUnitary_notMem` — **Corollary 4**.
* `lixLimit_hasK1InjWitness_of` — **the endpoint**, over `LemmaTwoHolds` alone.
-/

namespace GroupApproximation
namespace LIX

open scoped Matrix ComplexOrder CStarAlgebra

attribute [local instance 100000] GroupApproximation.LIX.instSpectralPartialOrder
                                  GroupApproximation.LIX.instSpectralStarOrderedRing

set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. Transport across the two index types -/

/-- The reindexing of the `E`-index types. -/
def eIdxEquiv (j : ℕ) : STW59.EIdx j ≃ (Fin 2 ⊕ CharClass.HIdx (lixDD j)) :=
  Equiv.sumCongr (Equiv.refl (Fin 2)) (hIdxEquiv j)

theorem reindex_fromBlocks_diag {m n n' : Type*} [DecidableEq m] [DecidableEq n]
    [DecidableEq n'] (e : n ≃ n') (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    Matrix.reindex (Equiv.sumCongr (Equiv.refl m) e) (Equiv.sumCongr (Equiv.refl m) e)
        (Matrix.fromBlocks A 0 0 D)
      = Matrix.fromBlocks A 0 0 (Matrix.reindex e e D) := by
  ext p q
  rcases p with p | p <;> rcases q with q | q <;> rfl

theorem matEval_fromBlocks {X : Type*} [TopologicalSpace X] {ι κ ι' κ' : Type*} (x : X)
    (A : Matrix ι κ C(X, ℂ)) (B : Matrix ι κ' C(X, ℂ)) (C : Matrix ι' κ C(X, ℂ))
    (D : Matrix ι' κ' C(X, ℂ)) :
    STW59.matEval x (Matrix.fromBlocks A B C D)
      = Matrix.fromBlocks (STW59.matEval x A) (STW59.matEval x B) (STW59.matEval x C)
        (STW59.matEval x D) := by
  ext p q
  rcases p with p | p <;> rcases q with q | q <;> rfl

theorem reindex_mul {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι') (M N : Matrix ι ι ℂ) :
    Matrix.reindex e e M * Matrix.reindex e e N = Matrix.reindex e e (M * N) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv]

theorem reindex_conjTranspose {ι ι' : Type*} (e : ι ≃ ι') (M : Matrix ι ι ℂ) :
    (Matrix.reindex e e M)ᴴ = Matrix.reindex e e Mᴴ := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.conjTranspose_submatrix]

/-- The unit of the corner, transported: it is the manuscript's `𝟏² ⊕ H`. -/
theorem reindex_matEval_Eproj (j : ℕ) (w : STW59.baseX j) :
    Matrix.reindex (eIdxEquiv j) (eIdxEquiv j) (STW59.matEval w (STW59.Eproj j))
      = cornerE (hMatY j) w.2 := by
  have h1 : STW59.matEval w (STW59.Eproj j)
      = Matrix.fromBlocks 1 0 0 (STW59.matEval w.2 (STW59.HprojY j)) := by
    rw [STW59.Eproj_def, matEval_fromBlocks, STW59.matEval_one, STW59.Hproj_eq_pullMat,
      STW59.matEval_pullMat]
    rfl
  rw [h1, eIdxEquiv, reindex_fromBlocks_diag, ← hMatY_reindex, cornerE]

/-! ## 2. The evaluated homotopy -/

/-- The homotopy, evaluated in the fibre over `(v, y)` and transported to the manuscript's
index type. -/
def evalW (j : ℕ) (f : ℝ → STW59.StageAlgebra j) (t : ℝ) (v : ↥STW59.sphereFour)
    (y : STW59.baseY j) :
    Matrix (Fin 2 ⊕ CharClass.HIdx (lixDD j)) (Fin 2 ⊕ CharClass.HIdx (lixDD j)) ℂ :=
  Matrix.reindex (eIdxEquiv j) (eIdxEquiv j) (STW59.stageEval j (v, y) (f t))

/-- The `H`-block of the climbed generator, transported. -/
def evalC (j : ℕ) (c : Matrix (STW59.HIdx j) (STW59.HIdx j) C(STW59.baseY j, ℂ))
    (y : STW59.baseY j) :
    Matrix (CharClass.HIdx (lixDD j)) (CharClass.HIdx (lixDD j)) ℂ :=
  Matrix.reindex (hIdxEquiv j) (hIdxEquiv j) (STW59.matEval y c)

theorem isCornerUnit_evalW (j : ℕ) {f : ℝ → STW59.StageAlgebra j}
    (hfs : ∀ t, star (f t) * f t = 1) (hfs' : ∀ t, f t * star (f t) = 1)
    (t : ℝ) (v : ↥STW59.sphereFour) (y : STW59.baseY j) :
    IsCornerUnit (hMatY j) y (evalW j f t v y) where
  star_mul := by
    rw [evalW, reindex_conjTranspose, reindex_mul, ← STW59.stageEval_star, ← STW59.stageEval_mul,
      hfs t, STW59.stageEval_one]
    exact reindex_matEval_Eproj j (v, y)
  mul_star := by
    rw [evalW, reindex_conjTranspose, reindex_mul, ← STW59.stageEval_star, ← STW59.stageEval_mul,
      hfs' t, STW59.stageEval_one]
    exact reindex_matEval_Eproj j (v, y)

theorem evalW_zero (j : ℕ) {f : ℝ → STW59.StageAlgebra j} (hf0 : f 0 = 1)
    (v : ↥STW59.sphereFour) (y : STW59.baseY j) :
    evalW j f 0 v y = cornerE (hMatY j) y := by
  rw [evalW, hf0, STW59.stageEval_one]
  exact reindex_matEval_Eproj j (v, y)

theorem evalW_one (j : ℕ) {f : ℝ → STW59.StageAlgebra j} {a : STW59.StageAlgebra j}
    (hf1 : f 1 = a) {c : Matrix (STW59.HIdx j) (STW59.HIdx j) C(STW59.baseY j, ℂ)}
    (hc : STW59.toFunctionMatrix (a : STW59.SectionAlgebra (STW59.baseX j) (STW59.EIdx j))
      = Matrix.fromBlocks (genMatAt j) 0 0 (STW59.pullMat (STW59.baseYproj j) c))
    (v : ↥STW59.sphereFour) (y : STW59.baseY j) :
    evalW j f 1 v y
      = Matrix.fromBlocks (genU2 (equatorEmb (v : EuclideanSpace ℝ (Fin 5)))) 0 0
        (evalC j c y) := by
  have h1 : STW59.stageEval j (v, y) (f 1)
      = Matrix.fromBlocks (genU2 (equatorEmb (v : EuclideanSpace ℝ (Fin 5)))) 0 0
        (STW59.matEval y c) := by
    rw [hf1, STW59.stageEval, ← STW59.matEval_toFunctionMatrix, hc, matEval_fromBlocks,
      STW59.matEval_pullMat, matEval_genMatAt]
    rfl
  rw [evalW, h1, eIdxEquiv, reindex_fromBlocks_diag, evalC]

theorem continuous_evalW (j : ℕ) {f : ℝ → STW59.StageAlgebra j} (hfc : Continuous f) :
    Continuous fun r : ℝ × ↥STW59.sphereFour × STW59.baseY j => evalW j f r.1 r.2.1 r.2.2 := by
  have h1 : Continuous fun r : ℝ × STW59.baseX j =>
      ((f r.1 : STW59.SectionAlgebra (STW59.baseX j) (STW59.EIdx j))) r.2 :=
    Continuous.eval ((continuous_subtype_val.comp hfc).comp continuous_fst) continuous_snd
  have h2 : Continuous fun r : ℝ × STW59.baseX j => STW59.stageEval j r.2 (f r.1) :=
    continuous_matrix fun s t => h1.matrix_elem s t
  exact Continuous.matrix_submatrix h2 _ _

theorem continuous_evalC (j : ℕ)
    (c : Matrix (STW59.HIdx j) (STW59.HIdx j) C(STW59.baseY j, ℂ)) :
    Continuous (evalC j c) := by
  have h : Continuous fun y : STW59.baseY j => STW59.matEval y c :=
    continuous_matrix fun s t => (c s t).continuous
  exact h.matrix_submatrix _ _

/-! ## 3. The two complements, in the field's vocabulary -/

theorem eHmat_eq_bigE (j : ℕ) (m : CharClass.baseM (lixDD j)) :
    CharClass.EHmat m = bigE (hMatY j) m.2 := by
  rw [CharClass.EHmat_eq_fromBlocks]
  rfl

theorem fHmat_eq_bigF (j : ℕ) (m : CharClass.baseM (lixDD j)) :
    CharClass.FHmat m = bigF (hMatY j) ((m.1 : Fin 3 → ℂ)) m.2 := by
  rw [CharClass.FHmat_eq_fromBlocks]
  rfl

theorem continuousMvNEquiv_symm {ι M : Type*} [Fintype ι] [TopologicalSpace M]
    {P Q : M → Matrix ι ι ℂ} (h : CharClass.ContinuousMvNEquiv P Q) :
    CharClass.ContinuousMvNEquiv Q P := by
  obtain ⟨w, hw, h1, h2⟩ := h
  refine ⟨fun m => (w m)ᴴ, hw.matrix_conjTranspose, fun m => ?_, fun m => ?_⟩
  · rw [Matrix.conjTranspose_conjTranspose]
    exact h2 m
  · rw [Matrix.conjTranspose_conjTranspose]
    exact h1 m

/-! ## 4. Corollary 4 -/

/-- **The argument of Corollary 4**, from an abstract path in the stage algebra: a
null-homotopy of an element of the generator's shape contradicts Lemma 2. -/
theorem false_of_path {j : ℕ}
    (hlem : ¬ CharClass.ContinuousMvNEquiv (CharClass.FHmat (dd := lixDD j))
      (CharClass.EHmat (dd := lixDD j)))
    {a : STW59.StageAlgebra j} (hshape : HasGeneratorShape j a)
    {f : ℝ → STW59.StageAlgebra j} (hfc : Continuous f)
    (hfs : ∀ t, star (f t) * f t = 1) (hfs' : ∀ t, f t * star (f t) = 1)
    (hf0 : f 0 = 1) (hf1 : f 1 = a) : False := by
  obtain ⟨c, hc⟩ := hshape
  have hWu := isCornerUnit_evalW j hfs hfs'
  have hcorner : ∀ y : STW59.baseY j,
      (evalC j c y)ᴴ * evalC j c y = hMatY j y ∧
        evalC j c y * (evalC j c y)ᴴ = hMatY j y := by
    intro y
    obtain ⟨v⟩ : Nonempty ↥STW59.sphereFour := inferInstance
    have h1 := (hWu 1 v y).star_mul
    have h2 := (hWu 1 v y).mul_star
    rw [evalW_one j hf1 hc] at h1 h2
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      fromBlocks_diag_mul_rect, cornerE] at h1 h2
    exact ⟨(Matrix.fromBlocks_inj.mp h1).2.2.2, (Matrix.fromBlocks_inj.mp h2).2.2.2⟩
  obtain ⟨G, hGc, hGu, hGconj⟩ :=
    exists_unitary_field_of_nullHomotopy (P := hMatY j) (c := evalC j c)
      (W := evalW j f) (continuous_hMatY j) (hMatY_mul_self j) (conjTranspose_hMatY j)
      (continuous_evalC j c) (fun y => (hcorner y).1) (fun y => (hcorner y).2)
      (continuous_evalW j hfc) hWu (evalW_zero j hf0) (fun v y => evalW_one j hf1 hc v y)
  refine not_exists_unitary_field (fun hEq => hlem (continuousMvNEquiv_symm hEq)) hGc hGu ?_
  intro m
  rw [eHmat_eq_bigE j m, fHmat_eq_bigF j m]
  exact hGconj m

/-- **Corollary 4.**  If Lemma 2 holds at stage `j`, the climbed generator is not in the
identity component of the unitary group of the stage algebra. -/
theorem climb_genUnitary_notMem (h : LemmaTwoHolds) (j : ℕ) (hj : 0 ≤ j) :
    unitaryHom (lixTower.climbHom hj) genUnitary
      ∉ unitaryComponentOne (STW59.StageAlgebra j) := by
  intro hmem
  obtain ⟨γ⟩ := mem_unitaryComponentOne_iff.mp hmem
  refine false_of_path (h.at_stage j) (hasGeneratorShape_climb j)
    (f := fun t => ((γ (Set.projIcc 0 1 zero_le_one t) :
      unitary (STW59.StageAlgebra j)) : STW59.StageAlgebra j)) ?_ ?_ ?_ ?_ ?_
  · exact continuous_subtype_val.comp (γ.continuous.comp continuous_projIcc)
  · intro t
    exact (γ (Set.projIcc 0 1 zero_le_one t)).2.1
  · intro t
    exact (γ (Set.projIcc 0 1 zero_le_one t)).2.2
  · have h0 : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = (0 : unitInterval) := Set.projIcc_left zero_le_one
    rw [h0, γ.source]
    rfl
  · have h1 : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = (1 : unitInterval) := Set.projIcc_right zero_le_one
    rw [h1, γ.target]
    rfl

/-! ## 5. The endpoint -/

/-- **The `K₁`-non-injectivity witness for the counterexample algebra**, over the single
topological input.  This is the theorem `cs-endpoint` consumes. -/
theorem lixLimit_hasK1InjWitness_of (h : LemmaTwoHolds) : HasK1InjWitness LIXLimit :=
  lixLimit_hasK1InjWitness genUnitary (fun j hj => climb_genUnitary_notMem h j hj)
    hdiag_genUnitary

end

end LIX
end GroupApproximation
