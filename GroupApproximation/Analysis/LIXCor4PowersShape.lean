import GroupApproximation.Analysis.LIXLimitAlgebra
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-`n` generator shape along the tower, for any top block on the sphere

`Analysis/LIXLemmaSixShape.lean` and `Analysis/LIXLemmaSixClimb.lean` prove, at rank two, that
the climbed generator is `u ⊕ c_j` **on the nose**: its `𝟏^n` block is the generator read at the
sphere coordinate, and its `H` block is pulled back from `Y_j`.  This file is the same statement
at every rank `n`, and for an arbitrary continuous top block
`U : S^{2n} → M_n(ℂ)` rather than for the one generator.

Two things are gained by the parameter, and both are consumed by the `k`-indexed Corollary 4.

* The endpoint witness of the stronger theorem is the **renormalised** generator `ũ = Aᴴ u`
  (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3), not `u`.  With `U` a parameter the shape
  of `ũ ⊕ 1_H` costs nothing.
* The `k`-th power of a stage unitary of shape `(U, c)` has shape `(U^k, c^k)`
  (`HasSphereShape.pow`).  So `(φ_{0,j} w₀)^k` is again an explicit block matrix, and the
  field argument runs on it verbatim.

As at rank two there is no homotopy and no connectedness of a unitary group anywhere: every block
`STW59.Gen.connect` adds is constant in the sphere coordinate, so the shape is reproduced one level
up by an equality.

## Main results

* `Gen.sphereMatAt` — a sphere-only top block, read over `X_j`.
* `Gen.HasSphereShape` — the shape predicate; `HasSphereShape.mul`, `HasSphereShape.pow`.
* `Gen.sphereStage`, `Gen.sphereUnitary` — `U ⊕ 1_{H₀}` in the stage-zero algebra.
* `Gen.HasSphereShape.connect`, `Gen.hasSphereShape_climb` — the shape at every stage.
-/

namespace GroupApproximation
namespace LIX
namespace Gen

open scoped Matrix Kronecker ComplexOrder CStarAlgebra

set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. A top block read at every stage -/

section SphereMat

variable {n : ℕ}

/-- A continuous matrix field on the sphere `S^{2n}`, read over the stage-`j` base
`X_j = S^{2n} × Y_j`: it depends on the sphere coordinate only. -/
def sphereMatAt (n j : ℕ) (U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ)
    (hU : Continuous U) : Matrix (Fin n) (Fin n) C(STW59.Gen.baseX n j, ℂ) :=
  Matrix.of fun a b => ⟨fun w => U w.1 a b, (hU.comp continuous_fst).matrix_elem a b⟩

@[simp]
theorem matEval_sphereMatAt (j : ℕ) (U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ)
    (hU : Continuous U) (w : STW59.Gen.baseX n j) :
    STW59.matEval w (sphereMatAt n j U hU) = U w.1 := rfl

/-- The base projections are the identity on the sphere coordinate, so pulling a sphere-only
block back one level gives the same block. -/
theorem pullMat_baseProj_sphereMatAt (j : ℕ)
    (U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ) (hU : Continuous U) :
    STW59.pullMat (STW59.Gen.baseProj n j) (sphereMatAt n j U hU) = sphereMatAt n (j + 1) U hU := by
  refine STW59.matrix_ext_of_matEval fun w => ?_
  rw [STW59.matEval_pullMat, matEval_sphereMatAt, matEval_sphereMatAt]
  rfl

theorem sphereMatAt_mul (j : ℕ) {U V : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ}
    (hU : Continuous U) (hV : Continuous V) :
    sphereMatAt n j U hU * sphereMatAt n j V hV
      = sphereMatAt n j (fun v => U v * V v) (hU.matrix_mul hV) := by
  refine STW59.matrix_ext_of_matEval fun w => ?_
  rw [STW59.matEval_mul, matEval_sphereMatAt, matEval_sphereMatAt, matEval_sphereMatAt]

theorem sphereMatAt_conjTranspose (j : ℕ)
    {U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ} (hU : Continuous U) :
    (sphereMatAt n j U hU)ᴴ
      = sphereMatAt n j (fun v => (U v)ᴴ) hU.matrix_conjTranspose := by
  refine STW59.matrix_ext_of_matEval fun w => ?_
  rw [STW59.matEval_conjTranspose, matEval_sphereMatAt, matEval_sphereMatAt]

theorem sphereMatAt_const_one (j : ℕ) :
    sphereMatAt n j (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) continuous_const = 1 := by
  refine STW59.matrix_ext_of_matEval fun w => ?_
  rw [matEval_sphereMatAt, STW59.matEval_one]

theorem sphereMatAt_congr (j : ℕ) {U V : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ}
    (hU : Continuous U) (hV : Continuous V) (h : ∀ v, U v = V v) :
    sphereMatAt n j U hU = sphereMatAt n j V hV := by
  obtain rfl : U = V := funext h
  rfl

theorem sphereMatAt_conjTranspose_mul (j : ℕ)
    {U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ} (hU : Continuous U)
    (hu : ∀ v, (U v)ᴴ * U v = 1) :
    (sphereMatAt n j U hU)ᴴ * sphereMatAt n j U hU = 1 := by
  refine STW59.matrix_ext_of_matEval fun w => ?_
  rw [STW59.matEval_mul, STW59.matEval_conjTranspose, matEval_sphereMatAt, STW59.matEval_one]
  exact hu w.1

theorem sphereMatAt_mul_conjTranspose (j : ℕ)
    {U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ} (hU : Continuous U)
    (hu : ∀ v, U v * (U v)ᴴ = 1) :
    sphereMatAt n j U hU * (sphereMatAt n j U hU)ᴴ = 1 := by
  refine STW59.matrix_ext_of_matEval fun w => ?_
  rw [STW59.matEval_mul, STW59.matEval_conjTranspose, matEval_sphereMatAt, STW59.matEval_one]
  exact hu w.1

end SphereMat

/-! ## 2. The shape predicate -/

section Shape

variable {n : ℕ}

/-- **`a` has the sphere shape `(U, c)` at stage `j`**: its `𝟏^n` block is `U` read at the sphere
coordinate, and its `H` block is pulled back from `Y_j`, so it does not see the sphere at all. -/
def HasSphereShape (n j : ℕ) (U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ)
    (hU : Continuous U) (a : STW59.Gen.StageAlgebra n j) : Prop :=
  ∃ c : Matrix (STW59.Gen.HIdx n j) (STW59.Gen.HIdx n j) C(STW59.Gen.baseY n j, ℂ),
    STW59.toFunctionMatrix (a : STW59.SectionAlgebra (STW59.Gen.baseX n j) (STW59.Gen.EIdx n j))
      = Matrix.fromBlocks (sphereMatAt n j U hU) 0 0 (STW59.pullMat (STW59.Gen.baseYproj n j) c)

theorem hasSphereShape_congr {j : ℕ} {U V : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ}
    (hU : Continuous U) (hV : Continuous V) (h : ∀ v, U v = V v)
    {a : STW59.Gen.StageAlgebra n j} (ha : HasSphereShape n j U hU a) :
    HasSphereShape n j V hV a := by
  obtain rfl : U = V := funext h
  exact ha

/-- **Products keep the shape**, blockwise. -/
theorem HasSphereShape.mul {j : ℕ} {U V : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ}
    {hU : Continuous U} {hV : Continuous V} {a b : STW59.Gen.StageAlgebra n j}
    (ha : HasSphereShape n j U hU a) (hb : HasSphereShape n j V hV b) :
    HasSphereShape n j (fun v => U v * V v) (hU.matrix_mul hV) (a * b) := by
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  refine ⟨c * d, ?_⟩
  have h1 : ((a * b : STW59.Gen.StageAlgebra n j) :
        STW59.SectionAlgebra (STW59.Gen.baseX n j) (STW59.Gen.EIdx n j))
      = (a : STW59.SectionAlgebra (STW59.Gen.baseX n j) (STW59.Gen.EIdx n j))
        * (b : STW59.SectionAlgebra (STW59.Gen.baseX n j) (STW59.Gen.EIdx n j)) := rfl
  rw [h1, STW59.toFunctionMatrix_mul, hc, hd, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [sphereMatAt_mul, ← STW59.pullMat_mul]

/-- The unit of `A_j` has the shape `(1, H_j)`. -/
theorem hasSphereShape_one (j : ℕ) :
    HasSphereShape n j (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) continuous_const
      (1 : STW59.Gen.StageAlgebra n j) := by
  refine ⟨STW59.Gen.HprojY n j, ?_⟩
  rw [STW59.Gen.coe_stageAlgebra_one, STW59.Gen.toFunctionMatrix_stageProj, STW59.Gen.Eproj_def,
    sphereMatAt_const_one, STW59.Gen.Hproj_eq_pullMat n j]

/-- **Powers keep the shape**: `(U ⊕ c)^k = U^k ⊕ c^k`. -/
theorem HasSphereShape.pow {j : ℕ} {U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ}
    {hU : Continuous U} {a : STW59.Gen.StageAlgebra n j} (ha : HasSphereShape n j U hU a) (k : ℕ) :
    HasSphereShape n j (fun v => U v ^ k) (hU.pow k) (a ^ k) := by
  induction k with
  | zero =>
      refine hasSphereShape_congr continuous_const (hU.pow 0) (fun v => (pow_zero (U v)).symm) ?_
      rw [pow_zero]
      exact hasSphereShape_one j
  | succ k ih =>
      refine hasSphereShape_congr ((hU.pow k).matrix_mul hU) (hU.pow (k + 1))
        (fun v => (pow_succ (U v) k).symm) ?_
      rw [pow_succ]
      exact ih.mul ha

end Shape

/-! ## 3. The top block as a unitary of the stage-zero algebra -/

section StageZero

variable {n : ℕ}

/-- `U ⊕ 1_{H₀}` as an element of the stage-zero algebra.  At stage zero `H₀ = 0`, so this is
`U` itself, packaged in the corner. -/
def sphereStage (n : ℕ) (U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ)
    (hU : Continuous U) : STW59.Gen.StageAlgebra n 0 :=
  ⟨STW59.ofFunctionMatrix (STW59.Gen.blockUnitary n 0 (sphereMatAt n 0 U hU)), by
    rw [STW59.Gen.mem_stageAlgebra_iff]
    show STW59.ofFunctionMatrix (STW59.Gen.Eproj n 0) *
        STW59.ofFunctionMatrix (STW59.Gen.blockUnitary n 0 (sphereMatAt n 0 U hU)) *
        STW59.ofFunctionMatrix (STW59.Gen.Eproj n 0)
      = STW59.ofFunctionMatrix (STW59.Gen.blockUnitary n 0 (sphereMatAt n 0 U hU))
    rw [← STW59.ofFunctionMatrix_mul, ← STW59.ofFunctionMatrix_mul,
      STW59.Gen.blockUnitary_mem_corner]⟩

theorem coe_sphereStage (U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ)
    (hU : Continuous U) :
    (sphereStage n U hU : STW59.SectionAlgebra (STW59.Gen.baseX n 0) (STW59.Gen.EIdx n 0))
      = STW59.ofFunctionMatrix (STW59.Gen.blockUnitary n 0 (sphereMatAt n 0 U hU)) := rfl

theorem sphereStage_star_mul {U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ}
    (hU : Continuous U) (hu : ∀ v, (U v)ᴴ * U v = 1) :
    star (sphereStage n U hU) * sphereStage n U hU = 1 := by
  refine STW59.corner_ext ?_
  show star (STW59.ofFunctionMatrix (STW59.Gen.blockUnitary n 0 (sphereMatAt n 0 U hU))) *
      STW59.ofFunctionMatrix (STW59.Gen.blockUnitary n 0 (sphereMatAt n 0 U hU))
    = STW59.Gen.stageProj n 0
  rw [← STW59.ofFunctionMatrix_star, ← STW59.ofFunctionMatrix_mul, Matrix.star_eq_conjTranspose,
    STW59.Gen.blockUnitary_star_mul n 0 (sphereMatAt_conjTranspose_mul 0 hU hu)]
  rfl

theorem sphereStage_mul_star {U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ}
    (hU : Continuous U) (hu : ∀ v, U v * (U v)ᴴ = 1) :
    sphereStage n U hU * star (sphereStage n U hU) = 1 := by
  refine STW59.corner_ext ?_
  show STW59.ofFunctionMatrix (STW59.Gen.blockUnitary n 0 (sphereMatAt n 0 U hU)) *
      star (STW59.ofFunctionMatrix (STW59.Gen.blockUnitary n 0 (sphereMatAt n 0 U hU)))
    = STW59.Gen.stageProj n 0
  rw [← STW59.ofFunctionMatrix_star, ← STW59.ofFunctionMatrix_mul, Matrix.star_eq_conjTranspose,
    STW59.Gen.blockUnitary_mul_star n 0 (sphereMatAt_mul_conjTranspose 0 hU hu)]
  rfl

/-- **`U ⊕ 1_{H₀}` as a unitary of `A₀`.** -/
def sphereUnitary (n : ℕ) (U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ)
    (hU : Continuous U) (hu₁ : ∀ v, (U v)ᴴ * U v = 1) (hu₂ : ∀ v, U v * (U v)ᴴ = 1) :
    unitary (STW59.Gen.StageAlgebra n 0) :=
  ⟨sphereStage n U hU, sphereStage_star_mul hU hu₁, sphereStage_mul_star hU hu₂⟩

@[simp]
theorem coe_sphereUnitary (U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ)
    (hU : Continuous U) (hu₁ : ∀ v, (U v)ᴴ * U v = 1) (hu₂ : ∀ v, U v * (U v)ᴴ = 1) :
    (sphereUnitary n U hU hu₁ hu₂ : STW59.Gen.StageAlgebra n 0) = sphereStage n U hU := rfl

/-- At stage zero the `H` block is empty, so `U ⊕ 1_{H₀}` has the shape `(U, 0)`. -/
theorem hasSphereShape_sphereStage (U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ)
    (hU : Continuous U) : HasSphereShape n 0 U hU (sphereStage n U hU) := by
  refine ⟨0, ?_⟩
  rw [coe_sphereStage, STW59.toFunctionMatrix_ofFunctionMatrix, STW59.Gen.blockUnitary_def,
    STW59.Gen.Hproj_zero, STW59.pullMat_zero]

end StageZero

/-! ## 4. The shape all the way up the tower -/

section Climb

variable {n : ℕ}

/-- Associativity of the block sum under `eIdxSucc`, in the form `STW59.Gen.Eproj_succ` uses it. -/
theorem reindex_eIdxSucc_fromBlocks {j : ℕ}
    (P : Matrix (Fin n) (Fin n) C(STW59.Gen.baseX n (j + 1), ℂ))
    (Q : Matrix (STW59.Gen.HIdx n j) (STW59.Gen.HIdx n j) C(STW59.Gen.baseX n (j + 1), ℂ))
    (N : Matrix (STW59.Gen.NIdx n j) (STW59.Gen.NIdx n j) C(STW59.Gen.baseX n (j + 1), ℂ)) :
    Matrix.reindex (STW59.Gen.eIdxSucc n j) (STW59.Gen.eIdxSucc n j)
        (Matrix.fromBlocks (Matrix.fromBlocks P 0 0 Q) 0 0 N)
      = Matrix.fromBlocks P 0 0 (Matrix.fromBlocks Q 0 0 N) := by
  ext a b
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;> rfl

theorem toFunctionMatrix_connect (j : ℕ) (a : STW59.Gen.StageAlgebra n j) :
    STW59.toFunctionMatrix
        ((STW59.Gen.connect n j a : STW59.Gen.StageAlgebra n (j + 1)) :
          STW59.SectionAlgebra (STW59.Gen.baseX n (j + 1)) (STW59.Gen.EIdx n (j + 1)))
      = STW59.Gen.connectMatrix n j
          (STW59.toFunctionMatrix
            (a : STW59.SectionAlgebra (STW59.Gen.baseX n j) (STW59.Gen.EIdx n j))) := rfl

/-- **The connecting map preserves the sphere shape.**  The rank-`n` form of the manuscript's
Lemma 6, as an equality rather than a homotopy. -/
theorem HasSphereShape.connect {j : ℕ}
    {U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ} {hU : Continuous U}
    {a : STW59.Gen.StageAlgebra n j} (h : HasSphereShape n j U hU a) :
    HasSphereShape n (j + 1) U hU (STW59.Gen.connect n j a) := by
  obtain ⟨c, hc⟩ := h
  show ∃ _, _
  rw [toFunctionMatrix_connect]
  unfold STW59.Gen.connectMatrix
  generalize STW59.Gen.compressMat n j
      (STW59.toFunctionMatrix
        (a : STW59.SectionAlgebra (STW59.Gen.baseX n j) (STW59.Gen.EIdx n j))) = N
  refine ⟨Matrix.fromBlocks (STW59.pullMat (STW59.Gen.baseYtrunc n j) c) 0 0
      (STW59.constMat (STW59.Gen.baseY n (j + 1)) N ⊗ₖ STW59.Gen.newLineY n j), ?_⟩
  have hinner :
      Matrix.fromBlocks
          (STW59.pullMat (STW59.Gen.baseYproj n (j + 1))
            (STW59.pullMat (STW59.Gen.baseYtrunc n j) c)) 0 0
          (STW59.pullMat (STW59.Gen.baseYproj n (j + 1))
            (STW59.constMat (STW59.Gen.baseY n (j + 1)) N ⊗ₖ STW59.Gen.newLineY n j))
        = STW59.pullMat (STW59.Gen.baseYproj n (j + 1))
            (Matrix.fromBlocks (STW59.pullMat (STW59.Gen.baseYtrunc n j) c) 0 0
              (STW59.constMat (STW59.Gen.baseY n (j + 1)) N ⊗ₖ STW59.Gen.newLineY n j)) := by
    rw [STW59.pullMat_fromBlocks, STW59.pullMat_zero, STW59.pullMat_zero]
  rw [hc, STW59.pullMat_fromBlocks, STW59.pullMat_zero, STW59.pullMat_zero,
    pullMat_baseProj_sphereMatAt, STW59.pullMat_comp, STW59.Gen.baseYproj_comp_baseProj,
    ← STW59.pullMat_comp, STW59.Gen.newLine_eq_pullMat,
    ← STW59.pullMat_constMat (STW59.Gen.baseYproj n (j + 1)) N, ← STW59.pullMat_kronecker,
    reindex_eIdxSucc_fromBlocks, hinner]
  rfl

/-- **The sphere shape at every stage.**  Stated at `(lixTower n).climb j 0`, the tower's own
iterated map, so that `CStarTower.climbHom_apply` joins it to the witness theorem by `rfl`. -/
theorem hasSphereShape_climb {j : ℕ} {U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ}
    {hU : Continuous U} {a : STW59.Gen.StageAlgebra n 0} (ha : HasSphereShape n 0 U hU a) :
    HasSphereShape n j U hU ((lixTower n).climb j 0 a) := by
  induction j with
  | zero =>
      rw [CStarTower.climb_self]
      exact ha
  | succ i ih =>
      rw [(lixTower n).climb_succ (Nat.zero_le i), lixTower_succHom]
      exact ih.connect

/-- **The `k`-th power of the climbed unitary has shape `(U^k, c^k)` at every stage.**  This is
the form the `k`-indexed Corollary 4 consumes: the climb is a unital ⋆-homomorphism, so it
commutes with powers, and the shape is then `HasSphereShape.pow`. -/
theorem hasSphereShape_climb_pow {j : ℕ}
    {U : ↥(STW59.Gen.sphereEven n) → Matrix (Fin n) (Fin n) ℂ} {hU : Continuous U}
    {a : STW59.Gen.StageAlgebra n 0} (ha : HasSphereShape n 0 U hU a) (k : ℕ) :
    HasSphereShape n j (fun v => U v ^ k) (hU.pow k) ((lixTower n).climbHom (Nat.zero_le j) a ^ k) := by
  exact (hasSphereShape_climb ha).pow k

end Climb

end

end Gen
end LIX
end GroupApproximation

open GroupApproximation.LIX.Gen

#audit_axioms HasSphereShape.mul
#audit_axioms HasSphereShape.pow
#audit_axioms sphereUnitary
#audit_axioms hasSphereShape_sphereStage
#audit_axioms HasSphereShape.connect
#audit_axioms hasSphereShape_climb
#audit_axioms hasSphereShape_climb_pow
