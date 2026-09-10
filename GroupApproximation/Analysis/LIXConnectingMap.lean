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

namespace Gen

variable (n : ℕ)


/-! ### The frame at the stage point -/

/-- **The orthonormal identification `E_i(x_i) ≅ ℂ^{r_i}`**, as an isometry
`s : Matrix (EIdx n i) (Fin (stageRank n i)) ℂ`. -/
def stageFrame (i : ℕ) : Matrix (EIdx n i) (Fin (stageRank n i)) ℂ :=
  (exists_frame (stageRank n i) (matEval (stagePoint n i) (Eproj n i))
    (isStarProjection_matEval (isStarProjection_Eproj n i) (stagePoint n i))
    (trace_matEval_Eproj n i (stagePoint n i))).choose

theorem stageFrame_isometry (i : ℕ) : (stageFrame n i)ᴴ * stageFrame n i = 1 :=
  (exists_frame (stageRank n i) (matEval (stagePoint n i) (Eproj n i))
    (isStarProjection_matEval (isStarProjection_Eproj n i) (stagePoint n i))
    (trace_matEval_Eproj n i (stagePoint n i))).choose_spec.1

theorem stageFrame_mul_conjTranspose (i : ℕ) :
    stageFrame n i * (stageFrame n i)ᴴ = matEval (stagePoint n i) (Eproj n i) :=
  (exists_frame (stageRank n i) (matEval (stagePoint n i) (Eproj n i))
    (isStarProjection_matEval (isStarProjection_Eproj n i) (stagePoint n i))
    (trace_matEval_Eproj n i (stagePoint n i))).choose_spec.2

/-! ### Compression through the frame -/

/-- **`compressMat n i M := sᴴ M(x_i) s`**, the manuscript's `a(x_i)` read as an `r_i × r_i`
matrix under the frame identification. -/
def compressMat (i : ℕ) (M : Matrix (EIdx n i) (EIdx n i) C(baseX n i, ℂ)) :
    Matrix (Fin (stageRank n i)) (Fin (stageRank n i)) ℂ :=
  (stageFrame n i)ᴴ * matEval (stagePoint n i) M * stageFrame n i

theorem compressMat_add (i : ℕ) (M N : Matrix (EIdx n i) (EIdx n i) C(baseX n i, ℂ)) :
    compressMat n i (M + N) = compressMat n i M + compressMat n i N := by
  show (stageFrame n i)ᴴ * matEval (stagePoint n i) (M + N) * stageFrame n i
      = (stageFrame n i)ᴴ * matEval (stagePoint n i) M * stageFrame n i +
        (stageFrame n i)ᴴ * matEval (stagePoint n i) N * stageFrame n i
  rw [matEval_add, Matrix.mul_add, Matrix.add_mul]

theorem compressMat_smul (i : ℕ) (c : ℂ) (M : Matrix (EIdx n i) (EIdx n i) C(baseX n i, ℂ)) :
    compressMat n i (c • M) = c • compressMat n i M := by
  show (stageFrame n i)ᴴ * matEval (stagePoint n i) (c • M) * stageFrame n i
      = c • ((stageFrame n i)ᴴ * matEval (stagePoint n i) M * stageFrame n i)
  rw [matEval_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- `Eproj n i` is a left unit, at the stage point, for the fibre value of any corner element. -/
theorem matEval_Eproj_stagePoint_left (i : ℕ) {M : Matrix (EIdx n i) (EIdx n i) C(baseX n i, ℂ)}
    (hM : Eproj n i * M * Eproj n i = M) :
    matEval (stagePoint n i) (Eproj n i) * matEval (stagePoint n i) M = matEval (stagePoint n i) M := by
  have h : matEval (stagePoint n i) (Eproj n i) * matEval (stagePoint n i) M *
      matEval (stagePoint n i) (Eproj n i) = matEval (stagePoint n i) M := by
    have hM' := congrArg (matEval (stagePoint n i)) hM
    rwa [matEval_mul, matEval_mul] at hM'
  calc matEval (stagePoint n i) (Eproj n i) * matEval (stagePoint n i) M
      = matEval (stagePoint n i) (Eproj n i) *
          (matEval (stagePoint n i) (Eproj n i) * matEval (stagePoint n i) M *
            matEval (stagePoint n i) (Eproj n i)) := by rw [h]
    _ = (matEval (stagePoint n i) (Eproj n i) * matEval (stagePoint n i) (Eproj n i)) *
          matEval (stagePoint n i) M * matEval (stagePoint n i) (Eproj n i) := by
        simp only [Matrix.mul_assoc]
    _ = matEval (stagePoint n i) (Eproj n i) * matEval (stagePoint n i) M *
          matEval (stagePoint n i) (Eproj n i) := by
        rw [(isStarProjection_matEval (isStarProjection_Eproj n i) (stagePoint n i)).isIdempotentElem.eq]
    _ = matEval (stagePoint n i) M := h

/-- **Compression is multiplicative on the corner.**  The identity `s sᴴ = E_i(x_i)` inserted
between the two factors collapses to the corner's own left unit on the second factor. -/
theorem compressMat_mul (i : ℕ) {M N : Matrix (EIdx n i) (EIdx n i) C(baseX n i, ℂ)}
    (hN : Eproj n i * N * Eproj n i = N) :
    compressMat n i (M * N) = compressMat n i M * compressMat n i N := by
  show (stageFrame n i)ᴴ * matEval (stagePoint n i) (M * N) * stageFrame n i
      = (stageFrame n i)ᴴ * matEval (stagePoint n i) M * stageFrame n i *
        ((stageFrame n i)ᴴ * matEval (stagePoint n i) N * stageFrame n i)
  rw [matEval_mul]
  have hN' : matEval (stagePoint n i) (Eproj n i) * matEval (stagePoint n i) N
      = matEval (stagePoint n i) N := matEval_Eproj_stagePoint_left n i hN
  have hss : stageFrame n i * (stageFrame n i)ᴴ = matEval (stagePoint n i) (Eproj n i) :=
    stageFrame_mul_conjTranspose n i
  calc (stageFrame n i)ᴴ * (matEval (stagePoint n i) M * matEval (stagePoint n i) N) * stageFrame n i
      = (stageFrame n i)ᴴ *
          (matEval (stagePoint n i) M *
            (matEval (stagePoint n i) (Eproj n i) * matEval (stagePoint n i) N)) * stageFrame n i := by
        rw [hN']
    _ = (stageFrame n i)ᴴ *
          (matEval (stagePoint n i) M *
            (stageFrame n i * (stageFrame n i)ᴴ * matEval (stagePoint n i) N)) * stageFrame n i := by
        rw [hss]
    _ = (stageFrame n i)ᴴ * matEval (stagePoint n i) M * stageFrame n i *
          ((stageFrame n i)ᴴ * matEval (stagePoint n i) N * stageFrame n i) := by
        simp only [Matrix.mul_assoc]

/-- **`compressMat n i (Eproj n i) = 1`**: the frame compresses the projection itself to the
identity, matching `newBlock n i`'s `1 ⊗ₖ L` shape exactly at the unit. -/
theorem compressMat_Eproj (i : ℕ) : compressMat n i (Eproj n i) = 1 := by
  show (stageFrame n i)ᴴ * matEval (stagePoint n i) (Eproj n i) * stageFrame n i = 1
  calc (stageFrame n i)ᴴ * matEval (stagePoint n i) (Eproj n i) * stageFrame n i
      = (stageFrame n i)ᴴ * (stageFrame n i * (stageFrame n i)ᴴ) * stageFrame n i := by
        rw [stageFrame_mul_conjTranspose n i]
    _ = ((stageFrame n i)ᴴ * stageFrame n i) * ((stageFrame n i)ᴴ * stageFrame n i) := by
        simp only [Matrix.mul_assoc]
    _ = 1 * 1 := by rw [stageFrame_isometry n i]
    _ = 1 := Matrix.one_mul 1

/-- Compression commutes with `ᴴ`, unconditionally (no corner hypothesis needed: `s`, unlike
the corner-membership argument of `compressMat_mul`, needs no help from the projection here). -/
theorem compressMat_conjTranspose (i : ℕ) (M : Matrix (EIdx n i) (EIdx n i) C(baseX n i, ℂ)) :
    (compressMat n i M)ᴴ = compressMat n i Mᴴ := by
  show ((stageFrame n i)ᴴ * matEval (stagePoint n i) M * stageFrame n i)ᴴ
      = (stageFrame n i)ᴴ * matEval (stagePoint n i) Mᴴ * stageFrame n i
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    ← matEval_conjTranspose]
  simp only [Matrix.mul_assoc]

/-! ### The block-diagonal cancellation lemma for `newBlock` -/

/-- `newBlock n i` is a left-and-right unit for `C ⊗ₖ newLine n i`, for any `C` (this is where
`newLine n i`'s idempotency is spent). -/
theorem newBlock_mul_kronecker_newBlock (i : ℕ)
    (C : Matrix (Fin (stageRank n i)) (Fin (stageRank n i)) C(baseX n (i + 1), ℂ)) :
    newBlock n i * (C ⊗ₖ newLine n i) * newBlock n i = C ⊗ₖ newLine n i := by
  show ((1 : Matrix (Fin (stageRank n i)) (Fin (stageRank n i)) C(baseX n (i + 1), ℂ)) ⊗ₖ newLine n i) *
      (C ⊗ₖ newLine n i) *
      ((1 : Matrix (Fin (stageRank n i)) (Fin (stageRank n i)) C(baseX n (i + 1), ℂ)) ⊗ₖ newLine n i)
    = C ⊗ₖ newLine n i
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, (isStarProjection_newLine n i).isIdempotentElem.eq]

/-- Kronecker product with `newLine n i` on the right is multiplicative, using its idempotency
to absorb the doubled copy of `newLine n i` that a naive `mul_kronecker_mul` would leave behind. -/
theorem compress_kronecker_mul (i : ℕ)
    (P Q : Matrix (Fin (stageRank n i)) (Fin (stageRank n i)) C(baseX n (i + 1), ℂ)) :
    (P * Q) ⊗ₖ newLine n i = (P ⊗ₖ newLine n i) * (Q ⊗ₖ newLine n i) := by
  rw [← Matrix.mul_kronecker_mul, (isStarProjection_newLine n i).isIdempotentElem.eq]

/-! ### The connecting map, at the level of matrices of functions -/

/-- **`φ_i(M) := π_i^* M ⊕ (constMat (compressMat n i M) ⊗ L_{i+1})`**, under the fixed
equivalence `eIdxSucc n i`; matched block-by-block against `Eproj_succ`. -/
def connectMatrix (i : ℕ) (M : Matrix (EIdx n i) (EIdx n i) C(baseX n i, ℂ)) :
    Matrix (EIdx n (i + 1)) (EIdx n (i + 1)) C(baseX n (i + 1), ℂ) :=
  Matrix.reindex (eIdxSucc n i) (eIdxSucc n i)
    (Matrix.fromBlocks (pullMat (baseProj n i) M) 0 0
      (constMat (baseX n (i + 1)) (compressMat n i M) ⊗ₖ newLine n i))

theorem connectMatrix_add (i : ℕ) (M N : Matrix (EIdx n i) (EIdx n i) C(baseX n i, ℂ)) :
    connectMatrix n i (M + N) = connectMatrix n i M + connectMatrix n i N := by
  show Matrix.reindex (eIdxSucc n i) (eIdxSucc n i)
      (Matrix.fromBlocks (pullMat (baseProj n i) (M + N)) 0 0
        (constMat (baseX n (i + 1)) (compressMat n i (M + N)) ⊗ₖ newLine n i))
    = Matrix.reindex (eIdxSucc n i) (eIdxSucc n i)
        (Matrix.fromBlocks (pullMat (baseProj n i) M) 0 0
          (constMat (baseX n (i + 1)) (compressMat n i M) ⊗ₖ newLine n i)) +
      Matrix.reindex (eIdxSucc n i) (eIdxSucc n i)
        (Matrix.fromBlocks (pullMat (baseProj n i) N) 0 0
          (constMat (baseX n (i + 1)) (compressMat n i N) ⊗ₖ newLine n i))
  rw [← reindex_add]
  refine congrArg (Matrix.reindex (eIdxSucc n i) (eIdxSucc n i)) ?_
  rw [Matrix.fromBlocks_add]
  simp only [add_zero]
  rw [pullMat_add, compressMat_add, constMat_add, Matrix.add_kronecker]

theorem connectMatrix_smul (i : ℕ) (c : ℂ) (M : Matrix (EIdx n i) (EIdx n i) C(baseX n i, ℂ)) :
    connectMatrix n i (c • M) = c • connectMatrix n i M := by
  show Matrix.reindex (eIdxSucc n i) (eIdxSucc n i)
      (Matrix.fromBlocks (pullMat (baseProj n i) (c • M)) 0 0
        (constMat (baseX n (i + 1)) (compressMat n i (c • M)) ⊗ₖ newLine n i))
    = c • Matrix.reindex (eIdxSucc n i) (eIdxSucc n i)
        (Matrix.fromBlocks (pullMat (baseProj n i) M) 0 0
          (constMat (baseX n (i + 1)) (compressMat n i M) ⊗ₖ newLine n i))
  rw [← reindex_smul]
  refine congrArg (Matrix.reindex (eIdxSucc n i) (eIdxSucc n i)) ?_
  rw [Matrix.fromBlocks_smul]
  simp only [smul_zero]
  rw [pullMat_smul, compressMat_smul, constMat_smul, Matrix.smul_kronecker]

theorem connectMatrix_mul (i : ℕ) {M N : Matrix (EIdx n i) (EIdx n i) C(baseX n i, ℂ)}
    (hN : Eproj n i * N * Eproj n i = N) :
    connectMatrix n i (M * N) = connectMatrix n i M * connectMatrix n i N := by
  show Matrix.reindex (eIdxSucc n i) (eIdxSucc n i)
      (Matrix.fromBlocks (pullMat (baseProj n i) (M * N)) 0 0
        (constMat (baseX n (i + 1)) (compressMat n i (M * N)) ⊗ₖ newLine n i))
    = Matrix.reindex (eIdxSucc n i) (eIdxSucc n i)
        (Matrix.fromBlocks (pullMat (baseProj n i) M) 0 0
          (constMat (baseX n (i + 1)) (compressMat n i M) ⊗ₖ newLine n i)) *
      Matrix.reindex (eIdxSucc n i) (eIdxSucc n i)
        (Matrix.fromBlocks (pullMat (baseProj n i) N) 0 0
          (constMat (baseX n (i + 1)) (compressMat n i N) ⊗ₖ newLine n i))
  rw [← reindex_mul]
  refine congrArg (Matrix.reindex (eIdxSucc n i) (eIdxSucc n i)) ?_
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
  rw [pullMat_mul, compressMat_mul n i hN, constMat_mul, compress_kronecker_mul]

theorem connectMatrix_Eproj (i : ℕ) : connectMatrix n i (Eproj n i) = Eproj n (i + 1) := by
  show Matrix.reindex (eIdxSucc n i) (eIdxSucc n i)
      (Matrix.fromBlocks (pullMat (baseProj n i) (Eproj n i)) 0 0
        (constMat (baseX n (i + 1)) (compressMat n i (Eproj n i)) ⊗ₖ newLine n i)) = Eproj n (i + 1)
  rw [compressMat_Eproj, constMat_one, Eproj_succ]
  rfl

theorem connectMatrix_conjTranspose (i : ℕ) (M : Matrix (EIdx n i) (EIdx n i) C(baseX n i, ℂ)) :
    connectMatrix n i Mᴴ = (connectMatrix n i M)ᴴ := by
  show Matrix.reindex (eIdxSucc n i) (eIdxSucc n i)
      (Matrix.fromBlocks (pullMat (baseProj n i) Mᴴ) 0 0
        (constMat (baseX n (i + 1)) (compressMat n i Mᴴ) ⊗ₖ newLine n i))
    = (Matrix.reindex (eIdxSucc n i) (eIdxSucc n i)
        (Matrix.fromBlocks (pullMat (baseProj n i) M) 0 0
          (constMat (baseX n (i + 1)) (compressMat n i M) ⊗ₖ newLine n i)))ᴴ
  rw [← reindex_conjTranspose]
  refine congrArg (Matrix.reindex (eIdxSucc n i) (eIdxSucc n i)) ?_
  rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero, Matrix.conjTranspose_zero,
    ← pullMat_conjTranspose, Matrix.conjTranspose_kronecker,
    conjTranspose_eq_of_isStarProjection (isStarProjection_newLine n i),
    ← constMat_conjTranspose, compressMat_conjTranspose]

/-- **The connecting map lands in the next corner.** -/
theorem eproj_mul_connectMatrix_mul_eproj (i : ℕ) {M : Matrix (EIdx n i) (EIdx n i) C(baseX n i, ℂ)}
    (hM : Eproj n i * M * Eproj n i = M) :
    Eproj n (i + 1) * connectMatrix n i M * Eproj n (i + 1) = connectMatrix n i M := by
  have hblock :
      Matrix.fromBlocks (pullMat (baseProj n i) (Eproj n i)) 0 0 (newBlock n i) *
          Matrix.fromBlocks (pullMat (baseProj n i) M) 0 0
            (constMat (baseX n (i + 1)) (compressMat n i M) ⊗ₖ newLine n i) *
          Matrix.fromBlocks (pullMat (baseProj n i) (Eproj n i)) 0 0 (newBlock n i)
        = Matrix.fromBlocks (pullMat (baseProj n i) M) 0 0
            (constMat (baseX n (i + 1)) (compressMat n i M) ⊗ₖ newLine n i) := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
    rw [← pullMat_mul, ← pullMat_mul, hM, newBlock_mul_kronecker_newBlock]
  unfold connectMatrix
  rw [Eproj_succ, ← reindex_mul, ← reindex_mul, hblock]

/-! ### The connecting map, at the level of the stage algebras -/

/-- **`φ_i : A_i → A_{i+1}`**, as a plain function. -/
def connectFun (i : ℕ) (a : StageAlgebra n i) : StageAlgebra n (i + 1) :=
  ⟨ofFunctionMatrix
      (connectMatrix n i (toFunctionMatrix (a : SectionAlgebra (baseX n i) (EIdx n i)))),
    mem_stageAlgebra_iff.mpr (by
      show ofFunctionMatrix (Eproj n (i + 1)) *
          ofFunctionMatrix
            (connectMatrix n i (toFunctionMatrix (a : SectionAlgebra (baseX n i) (EIdx n i))))
          * ofFunctionMatrix (Eproj n (i + 1))
        = ofFunctionMatrix
            (connectMatrix n i (toFunctionMatrix (a : SectionAlgebra (baseX n i) (EIdx n i))))
      rw [← ofFunctionMatrix_mul, ← ofFunctionMatrix_mul,
        eproj_mul_connectMatrix_mul_eproj n i (toFunctionMatrix_mem_corner a)])⟩

theorem connectFun_one (i : ℕ) : connectFun n i 1 = 1 := by
  refine corner_ext ?_
  show ofFunctionMatrix (connectMatrix n i
      (toFunctionMatrix ((1 : StageAlgebra n i) : SectionAlgebra (baseX n i) (EIdx n i))))
    = stageProj n (i + 1)
  rw [coe_stageAlgebra_one, toFunctionMatrix_stageProj, connectMatrix_Eproj]
  rfl

theorem connectFun_mul (i : ℕ) (a b : StageAlgebra n i) :
    connectFun n i (a * b) = connectFun n i a * connectFun n i b := by
  refine corner_ext ?_
  show ofFunctionMatrix (connectMatrix n i
      (toFunctionMatrix ((a * b : StageAlgebra n i) : SectionAlgebra (baseX n i) (EIdx n i))))
    = ofFunctionMatrix
        (connectMatrix n i (toFunctionMatrix (a : SectionAlgebra (baseX n i) (EIdx n i))))
      * ofFunctionMatrix
        (connectMatrix n i (toFunctionMatrix (b : SectionAlgebra (baseX n i) (EIdx n i))))
  rw [coe_corner_mul, toFunctionMatrix_mul,
    connectMatrix_mul n i (toFunctionMatrix_mem_corner b), ofFunctionMatrix_mul]

theorem connectFun_add (i : ℕ) (a b : StageAlgebra n i) :
    connectFun n i (a + b) = connectFun n i a + connectFun n i b := by
  refine corner_ext ?_
  show ofFunctionMatrix (connectMatrix n i
      (toFunctionMatrix ((a + b : StageAlgebra n i) : SectionAlgebra (baseX n i) (EIdx n i))))
    = ofFunctionMatrix
        (connectMatrix n i (toFunctionMatrix (a : SectionAlgebra (baseX n i) (EIdx n i))))
      + ofFunctionMatrix
        (connectMatrix n i (toFunctionMatrix (b : SectionAlgebra (baseX n i) (EIdx n i))))
  rw [coe_corner_add, toFunctionMatrix_add, connectMatrix_add, ofFunctionMatrix_add]

theorem connectFun_smul (i : ℕ) (c : ℂ) (a : StageAlgebra n i) :
    connectFun n i (c • a) = c • connectFun n i a := by
  refine corner_ext ?_
  show ofFunctionMatrix (connectMatrix n i
      (toFunctionMatrix ((c • a : StageAlgebra n i) : SectionAlgebra (baseX n i) (EIdx n i))))
    = c • ofFunctionMatrix
        (connectMatrix n i (toFunctionMatrix (a : SectionAlgebra (baseX n i) (EIdx n i))))
  rw [coe_corner_smul, toFunctionMatrix_smul, connectMatrix_smul, ofFunctionMatrix_smul]

theorem connectFun_star (i : ℕ) (a : StageAlgebra n i) :
    connectFun n i (star a) = star (connectFun n i a) := by
  refine corner_ext ?_
  show ofFunctionMatrix (connectMatrix n i
      (toFunctionMatrix ((star a : StageAlgebra n i) : SectionAlgebra (baseX n i) (EIdx n i))))
    = star (ofFunctionMatrix
        (connectMatrix n i (toFunctionMatrix (a : SectionAlgebra (baseX n i) (EIdx n i)))))
  rw [coe_corner_star, toFunctionMatrix_star, Matrix.star_eq_conjTranspose,
    connectMatrix_conjTranspose, ← Matrix.star_eq_conjTranspose, ofFunctionMatrix_star]

/-- **`φ_i` is injective.**  Its `(1,1)` block is `pullMat (baseProj n i) a`, and
`baseProj n i` is surjective, so the block alone already determines `a`. -/
theorem connectFun_injective (i : ℕ) : Function.Injective (connectFun n i) := by
  intro a b hab
  have h : ofFunctionMatrix
        (connectMatrix n i (toFunctionMatrix (a : SectionAlgebra (baseX n i) (EIdx n i))))
      = ofFunctionMatrix
        (connectMatrix n i (toFunctionMatrix (b : SectionAlgebra (baseX n i) (EIdx n i)))) :=
    congrArg Subtype.val hab
  have h' : connectMatrix n i (toFunctionMatrix (a : SectionAlgebra (baseX n i) (EIdx n i)))
      = connectMatrix n i (toFunctionMatrix (b : SectionAlgebra (baseX n i) (EIdx n i))) :=
    ofFunctionMatrix_injective h
  have h'' : Matrix.reindex (eIdxSucc n i) (eIdxSucc n i)
        (Matrix.fromBlocks
          (pullMat (baseProj n i) (toFunctionMatrix (a : SectionAlgebra (baseX n i) (EIdx n i)))) 0 0
          (constMat (baseX n (i + 1))
              (compressMat n i (toFunctionMatrix (a : SectionAlgebra (baseX n i) (EIdx n i))))
            ⊗ₖ newLine n i))
      = Matrix.reindex (eIdxSucc n i) (eIdxSucc n i)
        (Matrix.fromBlocks
          (pullMat (baseProj n i) (toFunctionMatrix (b : SectionAlgebra (baseX n i) (EIdx n i)))) 0 0
          (constMat (baseX n (i + 1))
              (compressMat n i (toFunctionMatrix (b : SectionAlgebra (baseX n i) (EIdx n i))))
            ⊗ₖ newLine n i)) := h'
  have h3 : pullMat (baseProj n i) (toFunctionMatrix (a : SectionAlgebra (baseX n i) (EIdx n i)))
      = pullMat (baseProj n i) (toFunctionMatrix (b : SectionAlgebra (baseX n i) (EIdx n i))) := by
    refine Matrix.ext fun x y => ?_
    have hxy := congrFun (congrFun h'' (eIdxSucc n i (Sum.inl x))) (eIdxSucc n i (Sum.inl y))
    simpa using hxy
  have h4 : toFunctionMatrix (a : SectionAlgebra (baseX n i) (EIdx n i))
      = toFunctionMatrix (b : SectionAlgebra (baseX n i) (EIdx n i)) :=
    pullMat_injective_of_surjective (basePr_surjective n (Nat.le_succ i)) h3
  exact corner_ext (toFunctionMatrix_injective h4)

/-! ### Bundling into a unital ⋆-algebra homomorphism -/

/-- `connectFun n i` as a monoid homomorphism. -/
def connectMonoidHom (i : ℕ) : StageAlgebra n i →* StageAlgebra n (i + 1) where
  toFun := connectFun n i
  map_one' := connectFun_one n i
  map_mul' := connectFun_mul n i

/-- `connectFun n i` as a ring homomorphism (`RingHom.mk'` derives `map_zero` from `map_add`
and the codomain's additive group structure, so it is not proved separately). -/
def connectRingHom (i : ℕ) : StageAlgebra n i →+* StageAlgebra n (i + 1) :=
  RingHom.mk' (connectMonoidHom n i) (connectFun_add n i)

/-- **`φ_i : A_i → A_{i+1}`, as a unital ⋆-algebra homomorphism over `ℂ`.** -/
def connect (i : ℕ) : StageAlgebra n i →⋆ₐ[ℂ] StageAlgebra n (i + 1) :=
  { AlgHom.mk' (connectRingHom n i) (connectFun_smul n i) with
    map_star' := connectFun_star n i }

@[simp]
theorem connect_apply (i : ℕ) (a : StageAlgebra n i) : connect n i a = connectFun n i a := rfl

/-- **`φ_i` is injective.** -/
theorem connect_injective (i : ℕ) : Function.Injective (connect n i) := connectFun_injective n i

end Gen

/-! ### The `n = 2` instance

Every declaration below is `Gen.<same name> 2`; none has a proof of its own.  The one
`_def` lemma is published because `Analysis/LIXLemmaSixClimb.lean` unfolds `connectMatrix`
by name with `rw`, and an equation lemma that unfolds to the generic name would leave the
next rewrite with no pattern. -/

/-- **The orthonormal identification `E_i(x_i) ≅ ℂ^{r_i}`.** -/
abbrev stageFrame (i : ℕ) : Matrix (EIdx i) (Fin (stageRank i)) ℂ := Gen.stageFrame 2 i

theorem stageFrame_isometry (i : ℕ) : (stageFrame i)ᴴ * stageFrame i = 1 :=
  Gen.stageFrame_isometry 2 i

theorem stageFrame_mul_conjTranspose (i : ℕ) :
    stageFrame i * (stageFrame i)ᴴ = matEval (stagePoint i) (Eproj i) :=
  Gen.stageFrame_mul_conjTranspose 2 i

/-- **`compressMat i M := sᴴ M(x_i) s`.** -/
abbrev compressMat (i : ℕ) (M : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)) :
    Matrix (Fin (stageRank i)) (Fin (stageRank i)) ℂ := Gen.compressMat 2 i M

theorem compressMat_add (i : ℕ) (M N : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)) :
    compressMat i (M + N) = compressMat i M + compressMat i N := Gen.compressMat_add 2 i M N

theorem compressMat_smul (i : ℕ) (c : ℂ) (M : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)) :
    compressMat i (c • M) = c • compressMat i M := Gen.compressMat_smul 2 i c M

theorem matEval_Eproj_stagePoint_left (i : ℕ) {M : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)}
    (hM : Eproj i * M * Eproj i = M) :
    matEval (stagePoint i) (Eproj i) * matEval (stagePoint i) M = matEval (stagePoint i) M :=
  Gen.matEval_Eproj_stagePoint_left 2 i hM

/-- **Compression is multiplicative on the corner.** -/
theorem compressMat_mul (i : ℕ) {M N : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)}
    (hN : Eproj i * N * Eproj i = N) :
    compressMat i (M * N) = compressMat i M * compressMat i N := Gen.compressMat_mul 2 i hN

theorem compressMat_Eproj (i : ℕ) : compressMat i (Eproj i) = 1 := Gen.compressMat_Eproj 2 i

theorem compressMat_conjTranspose (i : ℕ) (M : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)) :
    (compressMat i M)ᴴ = compressMat i Mᴴ := Gen.compressMat_conjTranspose 2 i M

theorem newBlock_mul_kronecker_newBlock (i : ℕ)
    (C : Matrix (Fin (stageRank i)) (Fin (stageRank i)) C(baseX (i + 1), ℂ)) :
    newBlock i * (C ⊗ₖ newLine i) * newBlock i = C ⊗ₖ newLine i :=
  Gen.newBlock_mul_kronecker_newBlock 2 i C

theorem compress_kronecker_mul (i : ℕ)
    (P Q : Matrix (Fin (stageRank i)) (Fin (stageRank i)) C(baseX (i + 1), ℂ)) :
    (P * Q) ⊗ₖ newLine i = (P ⊗ₖ newLine i) * (Q ⊗ₖ newLine i) :=
  Gen.compress_kronecker_mul 2 i P Q

/-- **`φ_i(M) := π_i^* M ⊕ (constMat (compressMat i M) ⊗ L_{i+1})`.** -/
def connectMatrix (i : ℕ) (M : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)) :
    Matrix (EIdx (i + 1)) (EIdx (i + 1)) C(baseX (i + 1), ℂ) := Gen.connectMatrix 2 i M

/-- The defining equation of `connectMatrix`, for consumers that unfold it by name. -/
theorem connectMatrix_def (i : ℕ) (M : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)) :
    connectMatrix i M = Matrix.reindex (eIdxSucc i) (eIdxSucc i)
      (Matrix.fromBlocks (pullMat (baseProj i) M) 0 0
        (constMat (baseX (i + 1)) (compressMat i M) ⊗ₖ newLine i)) := rfl

theorem connectMatrix_add (i : ℕ) (M N : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)) :
    connectMatrix i (M + N) = connectMatrix i M + connectMatrix i N :=
  Gen.connectMatrix_add 2 i M N

theorem connectMatrix_smul (i : ℕ) (c : ℂ) (M : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)) :
    connectMatrix i (c • M) = c • connectMatrix i M := Gen.connectMatrix_smul 2 i c M

theorem connectMatrix_mul (i : ℕ) {M N : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)}
    (hN : Eproj i * N * Eproj i = N) :
    connectMatrix i (M * N) = connectMatrix i M * connectMatrix i N :=
  Gen.connectMatrix_mul 2 i hN

theorem connectMatrix_Eproj (i : ℕ) : connectMatrix i (Eproj i) = Eproj (i + 1) :=
  Gen.connectMatrix_Eproj 2 i

theorem connectMatrix_conjTranspose (i : ℕ) (M : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)) :
    connectMatrix i Mᴴ = (connectMatrix i M)ᴴ := Gen.connectMatrix_conjTranspose 2 i M

/-- **The connecting map lands in the next corner.** -/
theorem eproj_mul_connectMatrix_mul_eproj (i : ℕ) {M : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ)}
    (hM : Eproj i * M * Eproj i = M) :
    Eproj (i + 1) * connectMatrix i M * Eproj (i + 1) = connectMatrix i M :=
  Gen.eproj_mul_connectMatrix_mul_eproj 2 i hM

/-- **`φ_i : A_i → A_{i+1}`**, as a plain function. -/
abbrev connectFun (i : ℕ) (a : StageAlgebra i) : StageAlgebra (i + 1) := Gen.connectFun 2 i a

theorem connectFun_one (i : ℕ) : connectFun i 1 = 1 := Gen.connectFun_one 2 i

theorem connectFun_mul (i : ℕ) (a b : StageAlgebra i) :
    connectFun i (a * b) = connectFun i a * connectFun i b := Gen.connectFun_mul 2 i a b

theorem connectFun_add (i : ℕ) (a b : StageAlgebra i) :
    connectFun i (a + b) = connectFun i a + connectFun i b := Gen.connectFun_add 2 i a b

theorem connectFun_smul (i : ℕ) (c : ℂ) (a : StageAlgebra i) :
    connectFun i (c • a) = c • connectFun i a := Gen.connectFun_smul 2 i c a

theorem connectFun_star (i : ℕ) (a : StageAlgebra i) :
    connectFun i (star a) = star (connectFun i a) := Gen.connectFun_star 2 i a

/-- **`φ_i` is injective.** -/
theorem connectFun_injective (i : ℕ) : Function.Injective (connectFun i) :=
  Gen.connectFun_injective 2 i

/-- `connectFun i` as a monoid homomorphism. -/
abbrev connectMonoidHom (i : ℕ) : StageAlgebra i →* StageAlgebra (i + 1) :=
  Gen.connectMonoidHom 2 i

/-- `connectFun i` as a ring homomorphism. -/
abbrev connectRingHom (i : ℕ) : StageAlgebra i →+* StageAlgebra (i + 1) :=
  Gen.connectRingHom 2 i

/-- **`φ_i : A_i → A_{i+1}`, as a unital ⋆-algebra homomorphism over `ℂ`.** -/
abbrev connect (i : ℕ) : StageAlgebra i →⋆ₐ[ℂ] StageAlgebra (i + 1) := Gen.connect 2 i

@[simp]
theorem connect_apply (i : ℕ) (a : StageAlgebra i) : connect i a = connectFun i a := rfl

/-- **`φ_i` is injective.** -/
theorem connect_injective (i : ℕ) : Function.Injective (connect i) := Gen.connect_injective 2 i

end

end STW59
end GroupApproximation
