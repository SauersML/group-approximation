import GroupApproximation.Analysis.LIXStageAlgebra
import Mathlib.Algebra.Star.StarAlgHom

set_option autoImplicit false

/-!
# The connecting maps `φ_i : A_i → A_{i+1}` of the STW LIX tower

The manuscript's twisted point evaluation
`φ_i(a)(x, z) = a(x) ⊕ (a(x_i) ⊗ 1_{L_{i+1}, z})`, built directly from
`STW59.Eproj_succ`'s block decomposition `E_{i+1} = π_i^* E_i ⊕ (𝟏_{r_i} ⊗ L_{i+1})`
(`Analysis/LIXBlockProjections.lean`) and the corner algebra `A_i = Γ(p)`
(`Analysis/LIXCornerAlgebra.lean`, `Analysis/LIXStageAlgebra.lean`).

## The construction

* `STW59.stageFrame i` — an isometry `ℂ^{r_i} → ℂ^{E_i}` realizing `s sᴴ = E_i(x_i)`
  (`STW59.exists_frame`), the manuscript's orthonormal identification `E_i(x_i) ≅ ℂ^{r_i}`.
* `STW59.compressMat i M := sᴴ M(x_i) s`, the compression of a fibre value at the stage
  point through the frame.  It is multiplicative *only* on the corner (`STW59.compressMat_mul`
  needs its second argument to satisfy the corner condition at `x_i`): this is exactly where
  the mathematics of the connecting map lives, `s sᴴ = E_i(x_i)` acting as the corner's local
  identity between the two factors of a product.
* `STW59.connectMatrix i M := π_i^* M ⊕ (constMat (compressMat i M) ⊗ L_{i+1})`, matched
  against `Eproj_succ`'s block shape under the *same* fixed equivalence `eIdxSucc i`.
* `STW59.connectFun i : StageAlgebra i → StageAlgebra (i+1)` applies `connectMatrix i` to the
  underlying matrix of a corner element (`STW59.toFunctionMatrix`) and repackages it; the
  membership proof is `STW59.eproj_mul_connectMatrix_mul_eproj`.
* `STW59.connect i : StageAlgebra i →⋆ₐ[ℂ] StageAlgebra (i+1)` bundles `connectFun i` into a
  unital ⋆-algebra homomorphism (`STW59.connectFun_one/_mul/_add/_smul/_star`).
* `STW59.connect_injective` — injective, because the (1,1) block is `pullMat (baseProj i) a`
  and `baseProj i` is *surjective* (`STW59.basePr_surjective`): a pullback along a surjection
  is injective (`STW59.pullMat_injective_of_surjective`).

## Design notes

Everything about `connectMatrix`'s algebraic behaviour is proved once, generically, as a
statement about `Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)` with an explicit corner-membership
*hypothesis* where needed (`Eproj i * M * Eproj i = M`); the `StageAlgebra`-level statements
(`connectFun_mul` etc.) are one-line transports of these through `toFunctionMatrix`/
`ofFunctionMatrix` and `Analysis/LIXStageAlgebra.lean`'s `toFunctionMatrix_mem_corner`.  This
keeps every `noncomm_ring`-flavoured computation confined to the `Matrix _ _ C(X, ℂ)` picture,
where there is no `CStarMatrix` instance diamond (memory:
`shared-tree-style-normalizer`/`cs-endpoint`'s TRAPS on `CStarMat`), and crosses into the
corner's abstract algebra structure only through named, already-verified bridge lemmas.
-/

namespace GroupApproximation
namespace STW59

open scoped Matrix Kronecker ComplexOrder CStarAlgebra

noncomputable section

/-! ### The frame at the stage point -/

/-- **The orthonormal identification `E_i(x_i) ≅ ℂ^{r_i}`**, as an isometry
`s : Matrix (EIdx i) (Fin (stageRank i)) ℂ`. -/
def stageFrame (i : ℕ) : Matrix (EIdx i) (Fin (stageRank i)) ℂ :=
  (exists_frame (stageRank i) (matEval (stagePoint i) (Eproj i))
    (isStarProjection_matEval (isStarProjection_Eproj i) (stagePoint i))
    (trace_matEval_Eproj i (stagePoint i))).choose

theorem stageFrame_isometry (i : ℕ) : (stageFrame i)ᴴ * stageFrame i = 1 :=
  (exists_frame (stageRank i) (matEval (stagePoint i) (Eproj i))
    (isStarProjection_matEval (isStarProjection_Eproj i) (stagePoint i))
    (trace_matEval_Eproj i (stagePoint i))).choose_spec.1

theorem stageFrame_mul_conjTranspose (i : ℕ) :
    stageFrame i * (stageFrame i)ᴴ = matEval (stagePoint i) (Eproj i) :=
  (exists_frame (stageRank i) (matEval (stagePoint i) (Eproj i))
    (isStarProjection_matEval (isStarProjection_Eproj i) (stagePoint i))
    (trace_matEval_Eproj i (stagePoint i))).choose_spec.2

/-! ### Compression through the frame -/

/-- **`compressMat i M := sᴴ M(x_i) s`**, the manuscript's `a(x_i)` read as an `r_i × r_i`
matrix under the frame identification. -/
def compressMat (i : ℕ) (M : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)) :
    Matrix (Fin (stageRank i)) (Fin (stageRank i)) ℂ :=
  (stageFrame i)ᴴ * matEval (stagePoint i) M * stageFrame i

theorem compressMat_add (i : ℕ) (M N : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)) :
    compressMat i (M + N) = compressMat i M + compressMat i N := by
  show (stageFrame i)ᴴ * matEval (stagePoint i) (M + N) * stageFrame i
      = (stageFrame i)ᴴ * matEval (stagePoint i) M * stageFrame i +
        (stageFrame i)ᴴ * matEval (stagePoint i) N * stageFrame i
  rw [matEval_add, Matrix.mul_add, Matrix.add_mul]

theorem compressMat_smul (i : ℕ) (c : ℂ) (M : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)) :
    compressMat i (c • M) = c • compressMat i M := by
  show (stageFrame i)ᴴ * matEval (stagePoint i) (c • M) * stageFrame i
      = c • ((stageFrame i)ᴴ * matEval (stagePoint i) M * stageFrame i)
  rw [matEval_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- `Eproj i` is a left unit, at the stage point, for the fibre value of any corner element. -/
theorem matEval_Eproj_stagePoint_left (i : ℕ) {M : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)}
    (hM : Eproj i * M * Eproj i = M) :
    matEval (stagePoint i) (Eproj i) * matEval (stagePoint i) M = matEval (stagePoint i) M := by
  have h : matEval (stagePoint i) (Eproj i) * matEval (stagePoint i) M *
      matEval (stagePoint i) (Eproj i) = matEval (stagePoint i) M := by
    have hM' := congrArg (matEval (stagePoint i)) hM
    rwa [matEval_mul, matEval_mul] at hM'
  calc matEval (stagePoint i) (Eproj i) * matEval (stagePoint i) M
      = matEval (stagePoint i) (Eproj i) *
          (matEval (stagePoint i) (Eproj i) * matEval (stagePoint i) M *
            matEval (stagePoint i) (Eproj i)) := by rw [h]
    _ = (matEval (stagePoint i) (Eproj i) * matEval (stagePoint i) (Eproj i)) *
          matEval (stagePoint i) M * matEval (stagePoint i) (Eproj i) := by
        simp only [Matrix.mul_assoc]
    _ = matEval (stagePoint i) (Eproj i) * matEval (stagePoint i) M *
          matEval (stagePoint i) (Eproj i) := by
        rw [(isStarProjection_matEval (isStarProjection_Eproj i) (stagePoint i)).isIdempotentElem.eq]
    _ = matEval (stagePoint i) M := h

/-- **Compression is multiplicative on the corner.**  The identity `s sᴴ = E_i(x_i)` inserted
between the two factors collapses to the corner's own left unit on the second factor. -/
theorem compressMat_mul (i : ℕ) {M N : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)}
    (hN : Eproj i * N * Eproj i = N) :
    compressMat i (M * N) = compressMat i M * compressMat i N := by
  show (stageFrame i)ᴴ * matEval (stagePoint i) (M * N) * stageFrame i
      = (stageFrame i)ᴴ * matEval (stagePoint i) M * stageFrame i *
        ((stageFrame i)ᴴ * matEval (stagePoint i) N * stageFrame i)
  rw [matEval_mul]
  have hN' : matEval (stagePoint i) (Eproj i) * matEval (stagePoint i) N
      = matEval (stagePoint i) N := matEval_Eproj_stagePoint_left i hN
  have hss : stageFrame i * (stageFrame i)ᴴ = matEval (stagePoint i) (Eproj i) :=
    stageFrame_mul_conjTranspose i
  calc (stageFrame i)ᴴ * (matEval (stagePoint i) M * matEval (stagePoint i) N) * stageFrame i
      = (stageFrame i)ᴴ *
          (matEval (stagePoint i) M *
            (matEval (stagePoint i) (Eproj i) * matEval (stagePoint i) N)) * stageFrame i := by
        rw [hN']
    _ = (stageFrame i)ᴴ *
          (matEval (stagePoint i) M *
            (stageFrame i * (stageFrame i)ᴴ * matEval (stagePoint i) N)) * stageFrame i := by
        rw [hss]
    _ = (stageFrame i)ᴴ * matEval (stagePoint i) M * stageFrame i *
          ((stageFrame i)ᴴ * matEval (stagePoint i) N * stageFrame i) := by
        simp only [Matrix.mul_assoc]

/-- **`compressMat i (Eproj i) = 1`**: the frame compresses the projection itself to the
identity, matching `newBlock i`'s `1 ⊗ₖ L` shape exactly at the unit. -/
theorem compressMat_Eproj (i : ℕ) : compressMat i (Eproj i) = 1 := by
  show (stageFrame i)ᴴ * matEval (stagePoint i) (Eproj i) * stageFrame i = 1
  calc (stageFrame i)ᴴ * matEval (stagePoint i) (Eproj i) * stageFrame i
      = (stageFrame i)ᴴ * (stageFrame i * (stageFrame i)ᴴ) * stageFrame i := by
        rw [stageFrame_mul_conjTranspose i]
    _ = ((stageFrame i)ᴴ * stageFrame i) * ((stageFrame i)ᴴ * stageFrame i) := by
        simp only [Matrix.mul_assoc]
    _ = 1 * 1 := by rw [stageFrame_isometry i]
    _ = 1 := Matrix.one_mul 1

/-- Compression commutes with `ᴴ`, unconditionally (no corner hypothesis needed: `s`, unlike
the corner-membership argument of `compressMat_mul`, needs no help from the projection here). -/
theorem compressMat_conjTranspose (i : ℕ) (M : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)) :
    (compressMat i M)ᴴ = compressMat i Mᴴ := by
  show ((stageFrame i)ᴴ * matEval (stagePoint i) M * stageFrame i)ᴴ
      = (stageFrame i)ᴴ * matEval (stagePoint i) Mᴴ * stageFrame i
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    ← matEval_conjTranspose]
  simp only [Matrix.mul_assoc]

/-! ### The block-diagonal cancellation lemma for `newBlock` -/

/-- `newBlock i` is a left-and-right unit for `C ⊗ₖ newLine i`, for any `C` (this is where
`newLine i`'s idempotency is spent). -/
theorem newBlock_mul_kronecker_newBlock (i : ℕ)
    (C : Matrix (Fin (stageRank i)) (Fin (stageRank i)) C(baseX (i + 1), ℂ)) :
    newBlock i * (C ⊗ₖ newLine i) * newBlock i = C ⊗ₖ newLine i := by
  show ((1 : Matrix (Fin (stageRank i)) (Fin (stageRank i)) C(baseX (i + 1), ℂ)) ⊗ₖ newLine i) *
      (C ⊗ₖ newLine i) *
      ((1 : Matrix (Fin (stageRank i)) (Fin (stageRank i)) C(baseX (i + 1), ℂ)) ⊗ₖ newLine i)
    = C ⊗ₖ newLine i
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, (isStarProjection_newLine i).isIdempotentElem.eq]

/-- Kronecker product with `newLine i` on the right is multiplicative, using its idempotency
to absorb the doubled copy of `newLine i` that a naive `mul_kronecker_mul` would leave behind. -/
theorem compress_kronecker_mul (i : ℕ)
    (P Q : Matrix (Fin (stageRank i)) (Fin (stageRank i)) C(baseX (i + 1), ℂ)) :
    (P * Q) ⊗ₖ newLine i = (P ⊗ₖ newLine i) * (Q ⊗ₖ newLine i) := by
  rw [← Matrix.mul_kronecker_mul, (isStarProjection_newLine i).isIdempotentElem.eq]

/-! ### The connecting map, at the level of matrices of functions -/

/-- **`φ_i(M) := π_i^* M ⊕ (constMat (compressMat i M) ⊗ L_{i+1})`**, under the fixed
equivalence `eIdxSucc i`; matched block-by-block against `Eproj_succ`. -/
def connectMatrix (i : ℕ) (M : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)) :
    Matrix (EIdx (i + 1)) (EIdx (i + 1)) C(baseX (i + 1), ℂ) :=
  Matrix.reindex (eIdxSucc i) (eIdxSucc i)
    (Matrix.fromBlocks (pullMat (baseProj i) M) 0 0
      (constMat (baseX (i + 1)) (compressMat i M) ⊗ₖ newLine i))

theorem connectMatrix_add (i : ℕ) (M N : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)) :
    connectMatrix i (M + N) = connectMatrix i M + connectMatrix i N := by
  show Matrix.reindex (eIdxSucc i) (eIdxSucc i)
      (Matrix.fromBlocks (pullMat (baseProj i) (M + N)) 0 0
        (constMat (baseX (i + 1)) (compressMat i (M + N)) ⊗ₖ newLine i))
    = Matrix.reindex (eIdxSucc i) (eIdxSucc i)
        (Matrix.fromBlocks (pullMat (baseProj i) M) 0 0
          (constMat (baseX (i + 1)) (compressMat i M) ⊗ₖ newLine i)) +
      Matrix.reindex (eIdxSucc i) (eIdxSucc i)
        (Matrix.fromBlocks (pullMat (baseProj i) N) 0 0
          (constMat (baseX (i + 1)) (compressMat i N) ⊗ₖ newLine i))
  rw [← reindex_add]
  refine congrArg (Matrix.reindex (eIdxSucc i) (eIdxSucc i)) ?_
  rw [Matrix.fromBlocks_add]
  simp only [add_zero]
  rw [pullMat_add, compressMat_add, constMat_add, Matrix.add_kronecker]

theorem connectMatrix_smul (i : ℕ) (c : ℂ) (M : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)) :
    connectMatrix i (c • M) = c • connectMatrix i M := by
  show Matrix.reindex (eIdxSucc i) (eIdxSucc i)
      (Matrix.fromBlocks (pullMat (baseProj i) (c • M)) 0 0
        (constMat (baseX (i + 1)) (compressMat i (c • M)) ⊗ₖ newLine i))
    = c • Matrix.reindex (eIdxSucc i) (eIdxSucc i)
        (Matrix.fromBlocks (pullMat (baseProj i) M) 0 0
          (constMat (baseX (i + 1)) (compressMat i M) ⊗ₖ newLine i))
  rw [← reindex_smul]
  refine congrArg (Matrix.reindex (eIdxSucc i) (eIdxSucc i)) ?_
  rw [Matrix.fromBlocks_smul]
  simp only [smul_zero]
  rw [pullMat_smul, compressMat_smul, constMat_smul, Matrix.smul_kronecker]

theorem connectMatrix_mul (i : ℕ) {M N : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)}
    (hN : Eproj i * N * Eproj i = N) :
    connectMatrix i (M * N) = connectMatrix i M * connectMatrix i N := by
  show Matrix.reindex (eIdxSucc i) (eIdxSucc i)
      (Matrix.fromBlocks (pullMat (baseProj i) (M * N)) 0 0
        (constMat (baseX (i + 1)) (compressMat i (M * N)) ⊗ₖ newLine i))
    = Matrix.reindex (eIdxSucc i) (eIdxSucc i)
        (Matrix.fromBlocks (pullMat (baseProj i) M) 0 0
          (constMat (baseX (i + 1)) (compressMat i M) ⊗ₖ newLine i)) *
      Matrix.reindex (eIdxSucc i) (eIdxSucc i)
        (Matrix.fromBlocks (pullMat (baseProj i) N) 0 0
          (constMat (baseX (i + 1)) (compressMat i N) ⊗ₖ newLine i))
  rw [← reindex_mul]
  refine congrArg (Matrix.reindex (eIdxSucc i) (eIdxSucc i)) ?_
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
  rw [pullMat_mul, compressMat_mul i hN, constMat_mul, compress_kronecker_mul]

theorem connectMatrix_Eproj (i : ℕ) : connectMatrix i (Eproj i) = Eproj (i + 1) := by
  show Matrix.reindex (eIdxSucc i) (eIdxSucc i)
      (Matrix.fromBlocks (pullMat (baseProj i) (Eproj i)) 0 0
        (constMat (baseX (i + 1)) (compressMat i (Eproj i)) ⊗ₖ newLine i)) = Eproj (i + 1)
  rw [compressMat_Eproj, constMat_one, Eproj_succ]
  rfl

theorem connectMatrix_conjTranspose (i : ℕ) (M : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)) :
    connectMatrix i Mᴴ = (connectMatrix i M)ᴴ := by
  show Matrix.reindex (eIdxSucc i) (eIdxSucc i)
      (Matrix.fromBlocks (pullMat (baseProj i) Mᴴ) 0 0
        (constMat (baseX (i + 1)) (compressMat i Mᴴ) ⊗ₖ newLine i))
    = (Matrix.reindex (eIdxSucc i) (eIdxSucc i)
        (Matrix.fromBlocks (pullMat (baseProj i) M) 0 0
          (constMat (baseX (i + 1)) (compressMat i M) ⊗ₖ newLine i)))ᴴ
  rw [← reindex_conjTranspose]
  refine congrArg (Matrix.reindex (eIdxSucc i) (eIdxSucc i)) ?_
  rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero, Matrix.conjTranspose_zero,
    ← pullMat_conjTranspose, Matrix.conjTranspose_kronecker,
    conjTranspose_eq_of_isStarProjection (isStarProjection_newLine i),
    ← constMat_conjTranspose, compressMat_conjTranspose]

/-- **The connecting map lands in the next corner.** -/
theorem eproj_mul_connectMatrix_mul_eproj (i : ℕ) {M : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)}
    (hM : Eproj i * M * Eproj i = M) :
    Eproj (i + 1) * connectMatrix i M * Eproj (i + 1) = connectMatrix i M := by
  have hblock :
      Matrix.fromBlocks (pullMat (baseProj i) (Eproj i)) 0 0 (newBlock i) *
          Matrix.fromBlocks (pullMat (baseProj i) M) 0 0
            (constMat (baseX (i + 1)) (compressMat i M) ⊗ₖ newLine i) *
          Matrix.fromBlocks (pullMat (baseProj i) (Eproj i)) 0 0 (newBlock i)
        = Matrix.fromBlocks (pullMat (baseProj i) M) 0 0
            (constMat (baseX (i + 1)) (compressMat i M) ⊗ₖ newLine i) := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
    rw [← pullMat_mul, ← pullMat_mul, hM, newBlock_mul_kronecker_newBlock]
  unfold connectMatrix
  rw [Eproj_succ, ← reindex_mul, ← reindex_mul, hblock]

/-! ### The connecting map, at the level of the stage algebras -/

/-- **`φ_i : A_i → A_{i+1}`**, as a plain function. -/
def connectFun (i : ℕ) (a : StageAlgebra i) : StageAlgebra (i + 1) :=
  ⟨ofFunctionMatrix
      (connectMatrix i (toFunctionMatrix (a : SectionAlgebra (baseX i) (EIdx i)))),
    mem_stageAlgebra_iff.mpr (by
      show ofFunctionMatrix (Eproj (i + 1)) *
          ofFunctionMatrix
            (connectMatrix i (toFunctionMatrix (a : SectionAlgebra (baseX i) (EIdx i))))
          * ofFunctionMatrix (Eproj (i + 1))
        = ofFunctionMatrix
            (connectMatrix i (toFunctionMatrix (a : SectionAlgebra (baseX i) (EIdx i))))
      rw [← ofFunctionMatrix_mul, ← ofFunctionMatrix_mul,
        eproj_mul_connectMatrix_mul_eproj i (toFunctionMatrix_mem_corner a)])⟩

theorem connectFun_one (i : ℕ) : connectFun i 1 = 1 := by
  refine corner_ext ?_
  show ofFunctionMatrix (connectMatrix i
      (toFunctionMatrix ((1 : StageAlgebra i) : SectionAlgebra (baseX i) (EIdx i))))
    = stageProj (i + 1)
  rw [coe_stageAlgebra_one, toFunctionMatrix_stageProj, connectMatrix_Eproj]
  rfl

theorem connectFun_mul (i : ℕ) (a b : StageAlgebra i) :
    connectFun i (a * b) = connectFun i a * connectFun i b := by
  refine corner_ext ?_
  show ofFunctionMatrix (connectMatrix i
      (toFunctionMatrix ((a * b : StageAlgebra i) : SectionAlgebra (baseX i) (EIdx i))))
    = ofFunctionMatrix
        (connectMatrix i (toFunctionMatrix (a : SectionAlgebra (baseX i) (EIdx i))))
      * ofFunctionMatrix
        (connectMatrix i (toFunctionMatrix (b : SectionAlgebra (baseX i) (EIdx i))))
  rw [coe_corner_mul, toFunctionMatrix_mul,
    connectMatrix_mul i (toFunctionMatrix_mem_corner b), ofFunctionMatrix_mul]

theorem connectFun_add (i : ℕ) (a b : StageAlgebra i) :
    connectFun i (a + b) = connectFun i a + connectFun i b := by
  refine corner_ext ?_
  show ofFunctionMatrix (connectMatrix i
      (toFunctionMatrix ((a + b : StageAlgebra i) : SectionAlgebra (baseX i) (EIdx i))))
    = ofFunctionMatrix
        (connectMatrix i (toFunctionMatrix (a : SectionAlgebra (baseX i) (EIdx i))))
      + ofFunctionMatrix
        (connectMatrix i (toFunctionMatrix (b : SectionAlgebra (baseX i) (EIdx i))))
  rw [coe_corner_add, toFunctionMatrix_add, connectMatrix_add, ofFunctionMatrix_add]

theorem connectFun_smul (i : ℕ) (c : ℂ) (a : StageAlgebra i) :
    connectFun i (c • a) = c • connectFun i a := by
  refine corner_ext ?_
  show ofFunctionMatrix (connectMatrix i
      (toFunctionMatrix ((c • a : StageAlgebra i) : SectionAlgebra (baseX i) (EIdx i))))
    = c • ofFunctionMatrix
        (connectMatrix i (toFunctionMatrix (a : SectionAlgebra (baseX i) (EIdx i))))
  rw [coe_corner_smul, toFunctionMatrix_smul, connectMatrix_smul, ofFunctionMatrix_smul]

theorem connectFun_star (i : ℕ) (a : StageAlgebra i) :
    connectFun i (star a) = star (connectFun i a) := by
  refine corner_ext ?_
  show ofFunctionMatrix (connectMatrix i
      (toFunctionMatrix ((star a : StageAlgebra i) : SectionAlgebra (baseX i) (EIdx i))))
    = star (ofFunctionMatrix
        (connectMatrix i (toFunctionMatrix (a : SectionAlgebra (baseX i) (EIdx i)))))
  rw [coe_corner_star, toFunctionMatrix_star, Matrix.star_eq_conjTranspose,
    connectMatrix_conjTranspose, ← Matrix.star_eq_conjTranspose, ofFunctionMatrix_star]

/-- **`φ_i` is injective.**  Its `(1,1)` block is `pullMat (baseProj i) a`, and
`baseProj i` is surjective, so the block alone already determines `a`. -/
theorem connectFun_injective (i : ℕ) : Function.Injective (connectFun i) := by
  intro a b hab
  have h : ofFunctionMatrix
        (connectMatrix i (toFunctionMatrix (a : SectionAlgebra (baseX i) (EIdx i))))
      = ofFunctionMatrix
        (connectMatrix i (toFunctionMatrix (b : SectionAlgebra (baseX i) (EIdx i)))) :=
    congrArg Subtype.val hab
  have h' : connectMatrix i (toFunctionMatrix (a : SectionAlgebra (baseX i) (EIdx i)))
      = connectMatrix i (toFunctionMatrix (b : SectionAlgebra (baseX i) (EIdx i))) :=
    ofFunctionMatrix_injective h
  have h'' : Matrix.reindex (eIdxSucc i) (eIdxSucc i)
        (Matrix.fromBlocks
          (pullMat (baseProj i) (toFunctionMatrix (a : SectionAlgebra (baseX i) (EIdx i)))) 0 0
          (constMat (baseX (i + 1))
              (compressMat i (toFunctionMatrix (a : SectionAlgebra (baseX i) (EIdx i))))
            ⊗ₖ newLine i))
      = Matrix.reindex (eIdxSucc i) (eIdxSucc i)
        (Matrix.fromBlocks
          (pullMat (baseProj i) (toFunctionMatrix (b : SectionAlgebra (baseX i) (EIdx i)))) 0 0
          (constMat (baseX (i + 1))
              (compressMat i (toFunctionMatrix (b : SectionAlgebra (baseX i) (EIdx i))))
            ⊗ₖ newLine i)) := h'
  have h3 : pullMat (baseProj i) (toFunctionMatrix (a : SectionAlgebra (baseX i) (EIdx i)))
      = pullMat (baseProj i) (toFunctionMatrix (b : SectionAlgebra (baseX i) (EIdx i))) := by
    refine Matrix.ext fun x y => ?_
    have hxy := congrFun (congrFun h'' (eIdxSucc i (Sum.inl x))) (eIdxSucc i (Sum.inl y))
    simpa using hxy
  have h4 : toFunctionMatrix (a : SectionAlgebra (baseX i) (EIdx i))
      = toFunctionMatrix (b : SectionAlgebra (baseX i) (EIdx i)) :=
    pullMat_injective_of_surjective (basePr_surjective (Nat.le_succ i)) h3
  exact corner_ext (toFunctionMatrix_injective h4)

/-! ### Bundling into a unital ⋆-algebra homomorphism -/

/-- `connectFun i` as a monoid homomorphism. -/
def connectMonoidHom (i : ℕ) : StageAlgebra i →* StageAlgebra (i + 1) where
  toFun := connectFun i
  map_one' := connectFun_one i
  map_mul' := connectFun_mul i

/-- `connectFun i` as a ring homomorphism (`RingHom.mk'` derives `map_zero` from `map_add`
and the codomain's additive group structure, so it is not proved separately). -/
def connectRingHom (i : ℕ) : StageAlgebra i →+* StageAlgebra (i + 1) :=
  RingHom.mk' (connectMonoidHom i) (connectFun_add i)

/-- **`φ_i : A_i → A_{i+1}`, as a unital ⋆-algebra homomorphism over `ℂ`.** -/
def connect (i : ℕ) : StageAlgebra i →⋆ₐ[ℂ] StageAlgebra (i + 1) :=
  { AlgHom.mk' (connectRingHom i) (connectFun_smul i) with
    map_star' := connectFun_star i }

@[simp]
theorem connect_apply (i : ℕ) (a : StageAlgebra i) : connect i a = connectFun i a := rfl

/-- **`φ_i` is injective.** -/
theorem connect_injective (i : ℕ) : Function.Injective (connect i) := connectFun_injective i

end

end STW59
end GroupApproximation
