import GroupApproximation.Analysis.LIXCor4PowersShape
import GroupApproximation.Analysis.LIXCor4PowersField
import GroupApproximation.Analysis.LIXLemmaSixHIdxGeneric
import GroupApproximation.Meta.AxiomGuard

/-!
# Corollary 4 at rank `n`, for powers, at every stage and at the limit

`Analysis/LIXLemmaSixCor4.lean` runs Corollary 4 at rank two: a null-homotopy of the climbed
generator `u ⊕ c_j` produces a continuous unitary field, which is the Murray--von Neumann
equivalence Lemma 2 denies.  This file runs the same argument at every rank `n` and for the `k`-th
power of any sphere-shaped stage unitary, which is the arrow the stronger theorem needs.

## What is new against rank two

* **The end of the null-homotopy is not the seam.**  For the `k`-th power the climbed unitary is
  `U^k ⊕ c^k` (`hasSphereShape_climb_pow`), while the seam the field glues across is
  `(g x)ᴴ · genU2 (ξ x)`.  The two are joined by a homotopy `H` of maps `S^{2n} → U(n)` that is
  *not* a path in the stage algebra, so the null-homotopy fed to the field is the concatenation
  `concatW`: the stage path at double speed, then `H ⊕ c^k`.  At `k = 1`, `ξ = id` and `g = 1`, `H`
  is constant and this is the rank-two argument.
* **The contradiction is stated against `LemmaTwoFor`'s own equivalence**, `FHmatOf n b ~ EHmat`,
  for the section `b m = ξ m.1`, so no symmetry step is needed at the end.

## Main results

* `Gen.false_of_path_gauged` — the argument, from an abstract path in the stage algebra.
* `Gen.climb_pow_notMem_gauged` — **Corollary 4 for powers at stage `j`**.
* `Gen.lixLimit_pow_notMem` — the tower argument: outside `U₀` at every stage gives outside `U₀`
  at the limit.
-/

namespace GroupApproximation
namespace LIX
namespace Gen

open scoped Matrix ComplexOrder CStarAlgebra

set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. Transport across the two index types -/

section Transport

variable {n : ℕ}

/-- The reindexing of the `E`-index types at rank `n`. -/
def eIdxEquiv (n j : ℕ) : STW59.Gen.EIdx n j ≃ (Fin n ⊕ CharClass.HIdx (lixDD n j)) :=
  Equiv.sumCongr (Equiv.refl (Fin n)) (hIdxEquiv n j)

theorem reindex_fromBlocks_diag {m k k' : Type*} [DecidableEq m] [DecidableEq k]
    [DecidableEq k'] (e : k ≃ k') (A : Matrix m m ℂ) (D : Matrix k k ℂ) :
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

/-- The unit of the corner, transported: it is the manuscript's `𝟏^n ⊕ H`. -/
theorem reindex_matEval_Eproj (n j : ℕ) (w : STW59.Gen.baseX n j) :
    Matrix.reindex (eIdxEquiv n j) (eIdxEquiv n j) (STW59.matEval w (STW59.Gen.Eproj n j))
      = cornerE n (hMatY n j) w.2 := by
  have h1 : STW59.matEval w (STW59.Gen.Eproj n j)
      = Matrix.fromBlocks 1 0 0 (STW59.matEval w.2 (STW59.Gen.HprojY n j)) := by
    rw [STW59.Gen.Eproj_def, matEval_fromBlocks, STW59.matEval_one, STW59.Gen.Hproj_eq_pullMat,
      STW59.matEval_pullMat]
    rfl
  rw [h1, eIdxEquiv, reindex_fromBlocks_diag, ← hMatY_reindex, cornerE]

end Transport

/-! ## 2. The evaluated homotopy -/

section Evaluated

variable {n : ℕ}

/-- The homotopy, evaluated in the fibre over `(v, y)` and transported to the manuscript's index
type. -/
def evalW (n j : ℕ) (f : ℝ → STW59.Gen.StageAlgebra n j) (t : ℝ) (v : ↥(STW59.Gen.sphereEven n))
    (y : STW59.Gen.baseY n j) :
    Matrix (Fin n ⊕ CharClass.HIdx (lixDD n j)) (Fin n ⊕ CharClass.HIdx (lixDD n j)) ℂ :=
  Matrix.reindex (eIdxEquiv n j) (eIdxEquiv n j) (STW59.Gen.stageEval n j (v, y) (f t))

/-- The `H`-block of a sphere-shaped stage element, transported. -/
def evalC (n j : ℕ)
    (c : Matrix (STW59.Gen.HIdx n j) (STW59.Gen.HIdx n j) C(STW59.Gen.baseY n j, ℂ))
    (y : STW59.Gen.baseY n j) :
    Matrix (CharClass.HIdx (lixDD n j)) (CharClass.HIdx (lixDD n j)) ℂ :=
  Matrix.reindex (hIdxEquiv n j) (hIdxEquiv n j) (STW59.matEval y c)

theorem isCornerUnit_evalW (n j : ℕ) {f : ℝ → STW59.Gen.StageAlgebra n j}
    (hfs : ∀ t, star (f t) * f t = 1) (hfs' : ∀ t, f t * star (f t) = 1)
    (t : ℝ) (v : ↥(STW59.Gen.sphereEven n)) (y : STW59.Gen.baseY n j) :
    IsCornerUnit n (hMatY n j) y (evalW n j f t v y) where
  star_mul := by
    rw [evalW, reindex_conjTranspose, reindex_mul, ← STW59.Gen.stageEval_star,
      ← STW59.Gen.stageEval_mul, hfs t, STW59.Gen.stageEval_one]
    exact reindex_matEval_Eproj n j (v, y)
  mul_star := by
    rw [evalW, reindex_conjTranspose, reindex_mul, ← STW59.Gen.stageEval_star,
      ← STW59.Gen.stageEval_mul, hfs' t, STW59.Gen.stageEval_one]
    exact reindex_matEval_Eproj n j (v, y)

theorem evalW_zero (n j : ℕ) {f : ℝ → STW59.Gen.StageAlgebra n j} (hf0 : f 0 = 1)
    (v : ↥(STW59.Gen.sphereEven n)) (y : STW59.Gen.baseY n j) :
    evalW n j f 0 v y = cornerE n (hMatY n j) y := by
  rw [evalW, hf0, STW59.Gen.stageEval_one]
  exact reindex_matEval_Eproj n j (v, y)

theorem evalW_one (n j : ℕ) {f : ℝ → STW59.Gen.StageAlgebra n j}
    {a : STW59.Gen.StageAlgebra n j} (hf1 : f 1 = a)
    {U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ} {hU : Continuous U}
    {c : Matrix (STW59.Gen.HIdx n j) (STW59.Gen.HIdx n j) C(STW59.Gen.baseY n j, ℂ)}
    (hc : STW59.toFunctionMatrix
        (a : STW59.SectionAlgebra (STW59.Gen.baseX n j) (STW59.Gen.EIdx n j))
      = Matrix.fromBlocks (sphereMatAt n j U hU) 0 0 (STW59.pullMat (STW59.Gen.baseYproj n j) c))
    (v : ↥(STW59.Gen.sphereEven n)) (y : STW59.Gen.baseY n j) :
    evalW n j f 1 v y = Matrix.fromBlocks (U v) 0 0 (evalC n j c y) := by
  have h1 : STW59.Gen.stageEval n j (v, y) (f 1)
      = Matrix.fromBlocks (U v) 0 0 (STW59.matEval y c) := by
    rw [hf1, STW59.Gen.stageEval, ← STW59.matEval_toFunctionMatrix, hc, matEval_fromBlocks,
      STW59.matEval_pullMat, matEval_sphereMatAt]
    rfl
  rw [evalW, h1, eIdxEquiv, reindex_fromBlocks_diag, evalC]

theorem continuous_evalW (n j : ℕ) {f : ℝ → STW59.Gen.StageAlgebra n j} (hfc : Continuous f) :
    Continuous fun r : ℝ × ↥(STW59.Gen.sphereEven n) × STW59.Gen.baseY n j =>
      evalW n j f r.1 r.2.1 r.2.2 := by
  have h1 : Continuous fun r : ℝ × STW59.Gen.baseX n j =>
      ((f r.1 : STW59.SectionAlgebra (STW59.Gen.baseX n j) (STW59.Gen.EIdx n j))) r.2 :=
    Continuous.eval ((continuous_subtype_val.comp hfc).comp continuous_fst) continuous_snd
  have h2 : Continuous fun r : ℝ × STW59.Gen.baseX n j => STW59.Gen.stageEval n j r.2 (f r.1) :=
    continuous_matrix fun s t => h1.matrix_elem s t
  exact Continuous.matrix_submatrix h2 _ _

theorem continuous_evalC (n j : ℕ)
    (c : Matrix (STW59.Gen.HIdx n j) (STW59.Gen.HIdx n j) C(STW59.Gen.baseY n j, ℂ)) :
    Continuous (evalC n j c) := by
  have h : Continuous fun y : STW59.Gen.baseY n j => STW59.matEval y c :=
    continuous_matrix fun s t => (c s t).continuous
  exact h.matrix_submatrix _ _

end Evaluated

/-! ## 3. The concatenated null-homotopy -/

section Concat

variable {n : ℕ}

/-- A unitary top block and a corner-unitary `H` block form a corner unit. -/
theorem isCornerUnit_diagBlock {HI : Type*} [Fintype HI] [DecidableEq HI] {Y : Type*}
    [TopologicalSpace Y] {P : Y → Matrix HI HI ℂ} {y : Y} {S : Matrix (Fin n) (Fin n) ℂ}
    {D : Matrix HI HI ℂ} (hS1 : Sᴴ * S = 1) (hS2 : S * Sᴴ = 1) (hD1 : Dᴴ * D = P y)
    (hD2 : D * Dᴴ = P y) : IsCornerUnit n P y (Matrix.fromBlocks S 0 0 D) where
  star_mul := by
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      fromBlocks_diag_mul_rect, hS1, hD1, cornerE]
  mul_star := by
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      fromBlocks_diag_mul_rect, hS2, hD2, cornerE]

/-- **The concatenated null-homotopy**: the stage path at double speed, then the sphere homotopy
`H` padded by the transported `H`-block. -/
def concatW (n j : ℕ) (f : ℝ → STW59.Gen.StageAlgebra n j)
    (H : ℝ → ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ)
    (c : Matrix (STW59.Gen.HIdx n j) (STW59.Gen.HIdx n j) C(STW59.Gen.baseY n j, ℂ))
    (t : ℝ) (v : ↥(STW59.Gen.sphereEven n)) (y : STW59.Gen.baseY n j) :
    Matrix (Fin n ⊕ CharClass.HIdx (lixDD n j)) (Fin n ⊕ CharClass.HIdx (lixDD n j)) ℂ :=
  if t ≤ 1 / 2 then evalW n j f (2 * t) v y
  else Matrix.fromBlocks (H (2 * t - 1) v) 0 0 (evalC n j c y)

theorem concatW_zero (n j : ℕ) (f : ℝ → STW59.Gen.StageAlgebra n j)
    (H : ℝ → ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ)
    (c : Matrix (STW59.Gen.HIdx n j) (STW59.Gen.HIdx n j) C(STW59.Gen.baseY n j, ℂ))
    (v : ↥(STW59.Gen.sphereEven n)) (y : STW59.Gen.baseY n j) :
    concatW n j f H c 0 v y = evalW n j f 0 v y := by
  rw [concatW, if_pos (by norm_num), mul_zero]

theorem concatW_one (n j : ℕ) (f : ℝ → STW59.Gen.StageAlgebra n j)
    (H : ℝ → ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ)
    (c : Matrix (STW59.Gen.HIdx n j) (STW59.Gen.HIdx n j) C(STW59.Gen.baseY n j, ℂ))
    (v : ↥(STW59.Gen.sphereEven n)) (y : STW59.Gen.baseY n j) :
    concatW n j f H c 1 v y = Matrix.fromBlocks (H 1 v) 0 0 (evalC n j c y) := by
  have e : (2 : ℝ) * 1 - 1 = 1 := by norm_num
  rw [concatW, if_neg (by norm_num), e]

theorem isCornerUnit_concatW (n j : ℕ) {f : ℝ → STW59.Gen.StageAlgebra n j}
    (hfs : ∀ t, star (f t) * f t = 1) (hfs' : ∀ t, f t * star (f t) = 1)
    {H : ℝ → ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ}
    (hHu1 : ∀ t v, (H t v)ᴴ * H t v = 1) (hHu2 : ∀ t v, H t v * (H t v)ᴴ = 1)
    {c : Matrix (STW59.Gen.HIdx n j) (STW59.Gen.HIdx n j) C(STW59.Gen.baseY n j, ℂ)}
    (hc1 : ∀ y, (evalC n j c y)ᴴ * evalC n j c y = hMatY n j y)
    (hc2 : ∀ y, evalC n j c y * (evalC n j c y)ᴴ = hMatY n j y)
    (t : ℝ) (v : ↥(STW59.Gen.sphereEven n)) (y : STW59.Gen.baseY n j) :
    IsCornerUnit n (hMatY n j) y (concatW n j f H c t v y) := by
  unfold concatW
  split_ifs
  · exact isCornerUnit_evalW n j hfs hfs' _ v y
  · exact isCornerUnit_diagBlock (hHu1 _ v) (hHu2 _ v) (hc1 y) (hc2 y)

theorem continuous_concatW (n j : ℕ) {f : ℝ → STW59.Gen.StageAlgebra n j} (hfc : Continuous f)
    {H : ℝ → ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ}
    (hHc : Continuous fun r : ℝ × ↥(STW59.Gen.sphereEven n) => H r.1 r.2)
    (c : Matrix (STW59.Gen.HIdx n j) (STW59.Gen.HIdx n j) C(STW59.Gen.baseY n j, ℂ))
    (hagree : ∀ v y, evalW n j f 1 v y = Matrix.fromBlocks (H 0 v) 0 0 (evalC n j c y)) :
    Continuous fun r : ℝ × ↥(STW59.Gen.sphereEven n) × STW59.Gen.baseY n j =>
      concatW n j f H c r.1 r.2.1 r.2.2 := by
  have hA : Continuous fun r : ℝ × ↥(STW59.Gen.sphereEven n) × STW59.Gen.baseY n j =>
      evalW n j f (2 * r.1) r.2.1 r.2.2 :=
    (continuous_evalW n j hfc).comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
  have hB : Continuous fun r : ℝ × ↥(STW59.Gen.sphereEven n) × STW59.Gen.baseY n j =>
      Matrix.fromBlocks (H (2 * r.1 - 1) r.2.1) 0 0 (evalC n j c r.2.2) :=
    Continuous.matrix_fromBlocks
      (hHc.comp (((continuous_const.mul continuous_fst).sub continuous_const).prodMk
        (continuous_fst.comp continuous_snd)))
      continuous_const continuous_const ((continuous_evalC n j c).comp (continuous_snd.comp continuous_snd))
  refine continuous_if_le continuous_fst continuous_const hA.continuousOn hB.continuousOn
    (fun r hr => ?_)
  have e1 : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  have e2 : (2 : ℝ) * (1 / 2) - 1 = 0 := by norm_num
  show evalW n j f (2 * r.1) r.2.1 r.2.2
    = Matrix.fromBlocks (H (2 * r.1 - 1) r.2.1) 0 0 (evalC n j c r.2.2)
  rw [hr, e2, e1]
  exact hagree _ _

end Concat

/-! ## 4. The comparison algebra at rank `n` -/

section Compare

variable {n : ℕ} {ℓ : ℕ} {dd : Fin ℓ → ℕ}

theorem isStarProjection_EHmat (m : CharClass.Gen.baseM n dd) :
    IsStarProjection (CharClass.Gen.EHmat n m) := by
  rw [CharClass.Gen.EHmat_eq_fromBlocks]
  exact STW59.isStarProjection_fromBlocks_diag
    (IsStarProjection.one_sub (STW59.isStarProjection_rankOneProj (CharClass.Gen.eLast_normSq n)))
    (CharClass.Gen.isStarProjection_Hmat m.2)

theorem continuous_EHmat (n : ℕ) : Continuous (CharClass.Gen.EHmat (dd := dd) n) :=
  (CharClass.Gen.continuous_Vmat n).sub continuous_const

/-- **The comparison algebra, in `LemmaTwoFor`'s direction.**  A continuous unitary field
conjugating the constant complement onto the complement of `b` gives the equivalence
`FHmatOf n b ~ EHmat n` that `LemmaTwoFor n dd b` denies. -/
theorem continuousMvNEquiv_of_unitary_field {b : CharClass.Gen.baseM n dd → Fin (n + 1) → ℂ}
    {G : CharClass.Gen.baseM n dd → Matrix (CharClass.Gen.VIdx n dd) (CharClass.Gen.VIdx n dd) ℂ}
    (hG : Continuous G) (hu : ∀ m, (G m)ᴴ * G m = 1)
    (hconj : ∀ m, G m * CharClass.Gen.EHmat n m * (G m)ᴴ = FHmatOf n b m) :
    CharClass.ContinuousMvNEquiv (FHmatOf n b) (CharClass.Gen.EHmat n) := by
  have hEs : ∀ m : CharClass.Gen.baseM n dd, (CharClass.Gen.EHmat n m)ᴴ = CharClass.Gen.EHmat n m :=
    fun m => STW59.conjTranspose_eq_of_isStarProjection (isStarProjection_EHmat m)
  refine ⟨fun m => (G m * CharClass.Gen.EHmat n m)ᴴ,
    (hG.matrix_mul (continuous_EHmat (dd := dd) n)).matrix_conjTranspose, fun m => ?_, fun m => ?_⟩
  · rw [Matrix.conjTranspose_conjTranspose]
    calc G m * CharClass.Gen.EHmat n m * (G m * CharClass.Gen.EHmat n m)ᴴ
        = G m * (CharClass.Gen.EHmat n m * CharClass.Gen.EHmat n m) * (G m)ᴴ := by
          rw [Matrix.conjTranspose_mul, hEs]
          simp only [Matrix.mul_assoc]
      _ = FHmatOf n b m := by
          rw [(isStarProjection_EHmat m).isIdempotentElem.eq, hconj m]
  · rw [Matrix.conjTranspose_conjTranspose]
    calc (G m * CharClass.Gen.EHmat n m)ᴴ * (G m * CharClass.Gen.EHmat n m)
        = CharClass.Gen.EHmat n m * ((G m)ᴴ * G m) * CharClass.Gen.EHmat n m := by
          rw [Matrix.conjTranspose_mul, hEs]
          simp only [Matrix.mul_assoc]
      _ = CharClass.Gen.EHmat n m := by
          rw [hu m, Matrix.mul_one, (isStarProjection_EHmat m).isIdempotentElem.eq]

theorem eHmat_eq_bigE (n j : ℕ) (m : CharClass.Gen.baseM n (lixDD n j)) :
    CharClass.Gen.EHmat n m = bigE n (hMatY n j) m.2 := by
  rw [CharClass.Gen.EHmat_eq_fromBlocks]
  rfl

theorem fHmatOf_eq_bigF (n j : ℕ) (b : CharClass.Gen.baseM n (lixDD n j) → Fin (n + 1) → ℂ)
    (m : CharClass.Gen.baseM n (lixDD n j)) :
    FHmatOf n b m = bigF n (hMatY n j) (b m) m.2 := by
  rw [FHmatOf, CharClass.Gen.Vmat, fromBlocks_sub]
  simp only [sub_zero]
  rfl

end Compare

/-! ## 5. Corollary 4 for powers -/

section Corollary

variable {n : ℕ}

/-- **The argument**, from an abstract path in the stage algebra.  A null-homotopy of a
sphere-shaped element `(U, c)`, followed by a sphere homotopy `H` from `U` to the gauged seam
`(g x)ᴴ · genU2 (ξ x)`, contradicts Lemma 2 for the section `ξ`. -/
theorem false_of_path_gauged {j : ℕ} {ξ : ↥(STW59.Gen.sphereOdd n) → Fin (n + 1) → ℂ}
    (hξ : IsCapDatum n ξ)
    (hlem : ¬ CharClass.ContinuousMvNEquiv
      (FHmatOf n (fun m : CharClass.Gen.baseM n (lixDD n j) => ξ m.1)) (CharClass.Gen.EHmat n))
    {g : ↥(STW59.Gen.sphereOdd n) → Matrix (Fin n) (Fin n) ℂ} (hgc : Continuous g)
    (hg1 : ∀ x, (g x)ᴴ * g x = 1) (hg2 : ∀ x, g x * (g x)ᴴ = 1)
    {U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ} {hU : Continuous U}
    {a : STW59.Gen.StageAlgebra n j} (hshape : HasSphereShape n j U hU a)
    {H : ℝ → ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ}
    (hHc : Continuous fun r : ℝ × ↥(STW59.Gen.sphereEven n) => H r.1 r.2)
    (hHu1 : ∀ t v, (H t v)ᴴ * H t v = 1) (hHu2 : ∀ t v, H t v * (H t v)ᴴ = 1)
    (hH0 : ∀ v, H 0 v = U v)
    (hH1 : ∀ x, capHeight n x = 0 → H 1 (dirPt n x) = (g x)ᴴ * genU2 n (ξ x))
    {f : ℝ → STW59.Gen.StageAlgebra n j} (hfc : Continuous f)
    (hfs : ∀ t, star (f t) * f t = 1) (hfs' : ∀ t, f t * star (f t) = 1)
    (hf0 : f 0 = 1) (hf1 : f 1 = a) : False := by
  obtain ⟨c, hc⟩ := hshape
  have hWu := isCornerUnit_evalW n j hfs hfs'
  have hcorner : ∀ y : STW59.Gen.baseY n j,
      (evalC n j c y)ᴴ * evalC n j c y = hMatY n j y ∧
        evalC n j c y * (evalC n j c y)ᴴ = hMatY n j y := by
    intro y
    obtain ⟨v⟩ : Nonempty ↥(STW59.Gen.sphereEven n) := inferInstance
    have h1 := (hWu 1 v y).star_mul
    have h2 := (hWu 1 v y).mul_star
    rw [evalW_one n j hf1 hc v y] at h1 h2
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      fromBlocks_diag_mul_rect, cornerE] at h1 h2
    exact ⟨(Matrix.fromBlocks_inj.mp h1).2.2.2, (Matrix.fromBlocks_inj.mp h2).2.2.2⟩
  have hagree : ∀ v y, evalW n j f 1 v y = Matrix.fromBlocks (H 0 v) 0 0 (evalC n j c y) :=
    fun v y => by rw [evalW_one n j hf1 hc v y, hH0]
  obtain ⟨G, hGc, hGu, hGconj⟩ :=
    exists_unitary_field_of_nullHomotopy_gauged (HI := CharClass.HIdx (lixDD n j))
      (Y := STW59.Gen.baseY n j) (P := hMatY n j) (c := evalC n j c) (W := concatW n j f H c)
      hξ hgc hg1 hg2 (continuous_hMatY n j) (hMatY_mul_self n j) (conjTranspose_hMatY n j)
      (continuous_evalC n j c) (fun y => (hcorner y).1) (fun y => (hcorner y).2)
      (continuous_concatW n j hfc hHc c hagree)
      (isCornerUnit_concatW n j hfs hfs' hHu1 hHu2 (fun y => (hcorner y).1)
        (fun y => (hcorner y).2))
      (fun v y => by rw [concatW_zero, evalW_zero n j hf0])
      (fun x hx y => by rw [concatW_one, hH1 x hx])
  refine hlem (continuousMvNEquiv_of_unitary_field (G := G) hGc (fun m => hGu m) ?_)
  intro m
  rw [eHmat_eq_bigE n j m, fHmatOf_eq_bigF n j _ m]
  exact hGconj m

/-- **Corollary 4 for powers, at stage `j`.**  If Lemma 2 holds for the section `ξ` at stage `j`,
and the `k`-th power of the top block `U` is homotopic through unitaries to the gauged seam at
`ξ`, then the `k`-th power of the climbed unitary is not in the identity component of `A_j`. -/
theorem climb_pow_notMem_gauged {ξ : ↥(STW59.Gen.sphereOdd n) → Fin (n + 1) → ℂ}
    (hξ : IsCapDatum n ξ)
    {g : ↥(STW59.Gen.sphereOdd n) → Matrix (Fin n) (Fin n) ℂ} (hgc : Continuous g)
    (hg1 : ∀ x, (g x)ᴴ * g x = 1) (hg2 : ∀ x, g x * (g x)ᴴ = 1)
    {U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ} {hU : Continuous U}
    (u : unitary (STW59.Gen.StageAlgebra n 0))
    (hshape : HasSphereShape n 0 U hU (u : STW59.Gen.StageAlgebra n 0)) (k : ℕ)
    {H : ℝ → ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ}
    (hHc : Continuous fun r : ℝ × ↥(STW59.Gen.sphereEven n) => H r.1 r.2)
    (hHu1 : ∀ t v, (H t v)ᴴ * H t v = 1) (hHu2 : ∀ t v, H t v * (H t v)ᴴ = 1)
    (hH0 : ∀ v, H 0 v = U v ^ k)
    (hH1 : ∀ x, capHeight n x = 0 → H 1 (dirPt n x) = (g x)ᴴ * genU2 n (ξ x)) (j : ℕ)
    (hlem : ¬ CharClass.ContinuousMvNEquiv
      (FHmatOf n (fun m : CharClass.Gen.baseM n (lixDD n j) => ξ m.1)) (CharClass.Gen.EHmat n)) :
    unitaryHom ((lixTower n).climbHom (Nat.zero_le j)) (u ^ k)
      ∉ unitaryComponentOne (STW59.Gen.StageAlgebra n j) := by
  intro hmem
  obtain ⟨γ⟩ := mem_unitaryComponentOne_iff.mp hmem
  refine false_of_path_gauged hξ hlem hgc hg1 hg2 (hasSphereShape_climb_pow hshape k) hHc hHu1
    hHu2 hH0 hH1
    (f := fun t => ((γ (Set.projIcc 0 1 zero_le_one t) :
      unitary (STW59.Gen.StageAlgebra n j)) : STW59.Gen.StageAlgebra n j)) ?_ ?_ ?_ ?_ ?_
  · exact continuous_subtype_val.comp (γ.continuous.comp continuous_projIcc)
  · intro t
    exact (γ (Set.projIcc 0 1 zero_le_one t)).2.1
  · intro t
    exact (γ (Set.projIcc 0 1 zero_le_one t)).2.2
  · have h0 : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = (0 : unitInterval) :=
      Set.projIcc_left zero_le_one
    rw [h0, γ.source]
    rfl
  · have h1 : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = (1 : unitInterval) :=
      Set.projIcc_right zero_le_one
    rw [h1, γ.target, coe_unitaryHom, SubmonoidClass.coe_pow, map_pow]

/-- **The tower argument for powers.**  If the `k`-th power of the climbed unitary is outside
`U₀` at every stage, the `k`-th power of its image in the limit is outside `U₀`. -/
theorem lixLimit_pow_notMem (n : ℕ) (u : unitary (STW59.Gen.StageAlgebra n 0)) (k : ℕ)
    (h : ∀ j : ℕ, unitaryHom ((lixTower n).climbHom (Nat.zero_le j)) (u ^ k)
      ∉ unitaryComponentOne (STW59.Gen.StageAlgebra n j)) :
    unitaryHom ((lixTower n).limIota 0) u ^ k ∉ unitaryComponentOne (LIXLimit n) := by
  rw [← map_pow]
  exact (lixTower n).notMem_unitaryComponentOne_limit fun j _ => h j

end Corollary

end

end Gen
end LIX
end GroupApproximation

open GroupApproximation.LIX.Gen

#audit_axioms false_of_path_gauged
#audit_axioms climb_pow_notMem_gauged
#audit_axioms lixLimit_pow_notMem
#audit_axioms continuousMvNEquiv_of_unitary_field
