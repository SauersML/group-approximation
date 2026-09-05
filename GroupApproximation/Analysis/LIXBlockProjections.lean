import GroupApproximation.Analysis.LIXProjectiveSpaceModel
import GroupApproximation.KTheory.MatrixProjection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# The block projections of the STW LIX construction

This file writes down, as explicit projection-valued matrix functions, the bundles of
the inductive system in §4 of
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`, and the
rank-two bundle `F` over `S^5` from §2.  Nothing here uses a vector-bundle library: a
bundle *is* a projection `p : Matrix ι ι C(X, ℂ)` and bundle isomorphism *is*
`GroupApproximation.MurrayVonNeumannEquiv`, as in
`GroupApproximation/KTheory/MatrixProjection.lean`.

## Model choices (other LIX lanes must match these exactly)

* `S^4 := STW59.sphereFour = Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1`, used as the
  subtype `↥STW59.sphereFour`.
* `S^5 ⊂ ℂ³ := STW59.sphereFive = STW59.unitVectors (Fin 3)`, a subset of the *plain*
  product space `Fin 3 → ℂ` cut out by `∑ i, ‖x i‖ ^ 2 = 1`.  **No `EuclideanSpace ℂ` and
  no `PiLp` anywhere**: coordinates are needed to write `x xᴴ`, and `PiLp` coordinate
  access has been an elaboration trap in this repo.
* `ℂP^d := STW59.CP d`, the matrix model of `Analysis/LIXProjectiveSpaceModel.lean`.
* Stage data: `r i = STW59.stageRank i = 2 ^ (i + 1)`,
  `Y i = STW59.baseY i = ∀ j : Fin i, CP (r j)`,
  `X i = STW59.baseX i = ↥sphereFour × baseY i`.
* Index types: `H i` is indexed by `STW59.HIdx i = Σ j : Fin i, Fin (r j + 1) × Fin (r j)`
  (the `j`-th summand contributes `r j` copies of the ambient `ℂ^{r j + 1}` of
  `CP^{r j}`), and `E i` by `STW59.EIdx i = Fin 2 ⊕ HIdx i`.
* Coefficients live in `C(X i, ℂ)`, so the block-diagonal assembly needs no continuity
  proof: `Matrix.blockDiagonal'` over a ring of continuous functions is continuous by
  construction.

## Main results

* `STW59.trace_Hproj`, `STW59.trace_Eproj`, `STW59.stageRank_sum`,
  `STW59.realDim_baseX` — the manuscript's (4.2): `rank H_i = r_i - 2`,
  `rank E_i = r_i`, `dim_ℝ X_i = 2 r_i`.
* `STW59.murrayVonNeumannEquiv_Fproj` — `F ⊕ 𝟏 ≅ 𝟏³` over `S^5`.
* `STW59.isLocallyConstant_trace` — the rank of a projection-valued function is locally
  constant, because it is a continuous `ℕ`-valued function
  (`STW59.exists_natCast_trace`).
-/

namespace GroupApproximation
namespace STW59

open scoped Matrix

noncomputable section

/-! ### Generic block lemmas -/

section Blocks

variable {A : Type*} [NonUnitalNonAssocSemiring A] [StarRing A]

theorem isStarProjection_blockDiagonal {o m : Type*} [DecidableEq o] [Fintype o] [Fintype m]
    {M : o → Matrix m m A} (h : ∀ k, IsStarProjection (M k)) :
    IsStarProjection (Matrix.blockDiagonal M) := by
  rw [isStarProjection_matrix_iff]
  constructor
  · rw [Matrix.blockDiagonal_conjTranspose]
    congr 1
    funext k
    exact conjTranspose_eq_of_isStarProjection (h k)
  · rw [← Matrix.blockDiagonal_mul]
    congr 1
    funext k
    exact (h k).isIdempotentElem.eq

theorem isStarProjection_blockDiagonal' {o : Type*} [DecidableEq o] [Fintype o]
    {m' : o → Type*} [∀ k, Fintype (m' k)] [∀ k, DecidableEq (m' k)]
    {M : ∀ k, Matrix (m' k) (m' k) A} (h : ∀ k, IsStarProjection (M k)) :
    IsStarProjection (Matrix.blockDiagonal' M) := by
  rw [isStarProjection_matrix_iff]
  constructor
  · rw [Matrix.blockDiagonal'_conjTranspose]
    congr 1
    funext k
    exact conjTranspose_eq_of_isStarProjection (h k)
  · rw [← Matrix.blockDiagonal'_mul]
    congr 1
    funext k
    exact (h k).isIdempotentElem.eq

theorem isStarProjection_fromBlocks_diag {l m : Type*} [Fintype l] [Fintype m]
    {P : Matrix l l A} {Q : Matrix m m A} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) : IsStarProjection (Matrix.fromBlocks P 0 0 Q) := by
  rw [isStarProjection_matrix_iff]
  constructor
  · simp [Matrix.fromBlocks_conjTranspose, conjTranspose_eq_of_isStarProjection hP,
      conjTranspose_eq_of_isStarProjection hQ]
  · rw [Matrix.fromBlocks_multiply]
    simp [hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq]

end Blocks

theorem trace_fromBlocks {l m R : Type*} [Fintype l] [Fintype m] [AddCommMonoid R]
    (P : Matrix l l R) (B : Matrix l m R) (C : Matrix m l R) (Q : Matrix m m R) :
    (Matrix.fromBlocks P B C Q).trace = P.trace + Q.trace := by
  simp [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type]

/-! ### The base spaces -/

/-- `S^4`, the unit sphere of `ℝ^5`. -/
abbrev sphereFour : Set (EuclideanSpace ℝ (Fin 5)) := Metric.sphere 0 1

/-- `S^5`, the unit sphere of `ℂ³` inside the plain product space `Fin 3 → ℂ`. -/
abbrev sphereFive : Set (Fin 3 → ℂ) := unitVectors (Fin 3)

instance sphereFive.instCompactSpace : CompactSpace ↥sphereFive :=
  isCompact_iff_compactSpace.mp (isCompact_unitVectors (Fin 3))

instance sphereFive.instNonempty : Nonempty ↥sphereFive := by
  classical
  refine Set.Nonempty.to_subtype ⟨fun i : Fin 3 => if i = 0 then (1 : ℂ) else 0, ?_⟩
  show (∑ i : Fin 3, ‖(if i = 0 then (1 : ℂ) else 0)‖ ^ 2) = 1
  rw [Finset.sum_eq_single (0 : Fin 3)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin 3)) h

/-! ### Stage data -/

/-- `r i = 2^{i+1}`, the rank of `E_i` in the manuscript's (4.1). -/
def stageRank (i : ℕ) : ℕ := 2 ^ (i + 1)

@[simp] theorem stageRank_zero : stageRank 0 = 2 := by simp [stageRank]

theorem stageRank_succ (i : ℕ) : stageRank (i + 1) = 2 * stageRank i := by
  unfold stageRank
  rw [pow_succ]
  ring

/-- The manuscript's `rank H_i = r_i - 2`, stated without truncated subtraction. -/
theorem stageRank_sum (i : ℕ) : (∑ j : Fin i, stageRank (j : ℕ)) + 2 = stageRank i := by
  induction i with
  | zero => simp [stageRank]
  | succ i ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [add_right_comm, ih, stageRank_succ]
      ring

/-- The manuscript's `dim_ℝ X_i = 2 r_i`: `X_i = S^4 × ∏_{j<i} ℂP^{r_j}` has real
dimension `4 + ∑_{j<i} 2 r_j`. -/
theorem realDim_baseX (i : ℕ) : 4 + ∑ j : Fin i, 2 * stageRank (j : ℕ) = 2 * stageRank i := by
  have h := stageRank_sum i
  rw [← Finset.mul_sum]
  omega

/-- `Y_i = ∏_{j<i} ℂP^{r_j}`. -/
abbrev baseY (i : ℕ) := ∀ j : Fin i, CP (stageRank (j : ℕ))

/-- `X_i = S^4 × Y_i`. -/
abbrev baseX (i : ℕ) := ↥sphereFour × baseY i

/-- The index set of `H_i = ⊕_{j<i} L_{j+1}^{⊕ r_j}`. -/
abbrev HIdx (i : ℕ) := Σ j : Fin i, Fin (stageRank (j : ℕ) + 1) × Fin (stageRank (j : ℕ))

/-- The index set of `E_i = 𝟏² ⊕ H_i`. -/
abbrev EIdx (i : ℕ) := Fin 2 ⊕ HIdx i

/-! ### The line bundles `L_{j+1}` pulled back to `X_i` -/

/-- The tautological line of the `j`-th projective factor, pulled back to `X_i`. -/
def lineProj (i : ℕ) (j : Fin i) :
    Matrix (Fin (stageRank (j : ℕ) + 1)) (Fin (stageRank (j : ℕ) + 1)) C(baseX i, ℂ) :=
  Matrix.of fun a b =>
    ⟨fun z => ((z.2 j : CP (stageRank (j : ℕ))) :
        Matrix (Fin (stageRank (j : ℕ) + 1)) (Fin (stageRank (j : ℕ) + 1)) ℂ) a b,
      (continuous_subtype_val.comp ((continuous_apply j).comp continuous_snd)).matrix_elem a b⟩

@[simp]
theorem matEval_lineProj (i : ℕ) (j : Fin i) (z : baseX i) :
    matEval z (lineProj i j) = taut (stageRank (j : ℕ)) (z.2 j) := by
  ext a b
  rfl

theorem isStarProjection_lineProj (i : ℕ) (j : Fin i) : IsStarProjection (lineProj i j) := by
  refine isStarProjection_of_forall_matEval fun z => ?_
  rw [matEval_lineProj]
  exact isStarProjection_taut _ _

theorem trace_lineProj (i : ℕ) (j : Fin i) : Matrix.trace (lineProj i j) = 1 := by
  refine ContinuousMap.ext fun z => ?_
  rw [← trace_matEval, matEval_lineProj, trace_taut]
  rfl

/-! ### `H_i` and `E_i` -/

/-- `H_i = ⊕_{j<i} L_{j+1}^{⊕ r_j}`, as an explicit block-diagonal projection-valued
continuous function on `X_i`. -/
def Hproj (i : ℕ) : Matrix (HIdx i) (HIdx i) C(baseX i, ℂ) :=
  Matrix.blockDiagonal' fun j : Fin i =>
    Matrix.blockDiagonal fun _ : Fin (stageRank (j : ℕ)) => lineProj i j

/-- `E_i = 𝟏² ⊕ H_i`. -/
def Eproj (i : ℕ) : Matrix (EIdx i) (EIdx i) C(baseX i, ℂ) :=
  Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) C(baseX i, ℂ)) 0 0 (Hproj i)

theorem Hproj_def (i : ℕ) : Hproj i = Matrix.blockDiagonal' fun j : Fin i =>
    Matrix.blockDiagonal fun _ : Fin (stageRank (j : ℕ)) => lineProj i j := rfl

theorem Eproj_def (i : ℕ) : Eproj i =
    Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) C(baseX i, ℂ)) 0 0 (Hproj i) := rfl

theorem isStarProjection_Hproj (i : ℕ) : IsStarProjection (Hproj i) :=
  Hproj_def i ▸ isStarProjection_blockDiagonal' fun j =>
    isStarProjection_blockDiagonal fun _ => isStarProjection_lineProj i j

theorem isStarProjection_Eproj (i : ℕ) : IsStarProjection (Eproj i) :=
  Eproj_def i ▸ isStarProjection_fromBlocks_diag (IsStarProjection.one _) (isStarProjection_Hproj i)

/-- **`rank H_i = r_i - 2`**, in the untruncated form `trace H_i = ∑_{j<i} r_j`. -/
theorem trace_Hproj (i : ℕ) :
    Matrix.trace (Hproj i) = ((∑ j : Fin i, stageRank (j : ℕ) : ℕ) : C(baseX i, ℂ)) := by
  rw [Hproj_def, Matrix.trace_blockDiagonal']
  have h : ∀ j : Fin i,
      Matrix.trace (Matrix.blockDiagonal fun _ : Fin (stageRank (j : ℕ)) => lineProj i j)
        = ((stageRank (j : ℕ) : ℕ) : C(baseX i, ℂ)) := by
    intro j
    rw [Matrix.trace_blockDiagonal]
    simp [trace_lineProj]
  rw [Finset.sum_congr rfl (fun j _ => h j)]
  push_cast
  ring

/-- **`rank E_i = r_i`.** -/
theorem trace_Eproj (i : ℕ) :
    Matrix.trace (Eproj i) = ((stageRank i : ℕ) : C(baseX i, ℂ)) := by
  rw [Eproj_def, trace_fromBlocks, Matrix.trace_one, trace_Hproj, Fintype.card_fin]
  rw [← stageRank_sum i]
  push_cast
  ring

/-! ### `F` over `S^5 ⊂ ℂ³` -/

/-- The tautological column vector `x` over `S^5`. -/
def hopfCol : Matrix (Fin 3) (Fin 1) C(↥sphereFive, ℂ) :=
  Matrix.of fun a _ =>
    ⟨fun x => (x : Fin 3 → ℂ) a, (continuous_apply a).comp continuous_subtype_val⟩

@[simp]
theorem hopfCol_apply (a : Fin 3) (u : Fin 1) (x : ↥sphereFive) :
    hopfCol a u x = (x : Fin 3 → ℂ) a := rfl

/-- The tautological line `x xᴴ` over `S^5` (the pullback of the tautological line of
`ℂP²` along the Hopf map). -/
def hopfProj : Matrix (Fin 3) (Fin 3) C(↥sphereFive, ℂ) := hopfCol * hopfColᴴ

theorem hopfProj_def : hopfProj = hopfCol * hopfColᴴ := rfl

theorem matEval_hopfProj (x : ↥sphereFive) :
    matEval x hopfProj = rankOneProj ((x : Fin 3 → ℂ)) := by
  rw [hopfProj_def, matEval_mul, matEval_conjTranspose]
  ext a b
  rw [Matrix.mul_apply]
  simp [Matrix.conjTranspose_apply]

theorem isStarProjection_hopfProj : IsStarProjection hopfProj := by
  refine isStarProjection_of_forall_matEval fun x => ?_
  rw [matEval_hopfProj]
  exact isStarProjection_rankOneProj x.2

theorem hopfCol_conjTranspose_mul : hopfColᴴ * hopfCol = 1 := by
  refine matrix_ext_of_matEval fun x => ?_
  rw [matEval_mul, matEval_conjTranspose, matEval_one]
  ext u v
  rw [Matrix.mul_apply]
  have hterm : ∀ a : Fin 3,
      ((matEval x hopfCol)ᴴ) u a * (matEval x hopfCol) a v
        = star ((x : Fin 3 → ℂ) a) * (x : Fin 3 → ℂ) a := by
    intro a
    simp [Matrix.conjTranspose_apply]
  rw [Finset.sum_congr rfl (fun a _ => hterm a), sum_star_mul_self x.2]
  have huv : u = v := Subsingleton.elim u v
  subst huv
  simp

theorem trace_hopfProj : Matrix.trace hopfProj = 1 := by
  refine ContinuousMap.ext fun x => ?_
  rw [← trace_matEval, matEval_hopfProj, trace_rankOneProj x.2]
  rfl

/-- **`F`**: the rank-two bundle `F_x = {w ∈ ℂ³ : ⟨w, x⟩ = 0}` over `S^5`, written as the
projection `x ↦ 1 - x xᴴ`. -/
def Fproj : Matrix (Fin 3) (Fin 3) C(↥sphereFive, ℂ) := 1 - hopfProj

theorem Fproj_def : Fproj = 1 - hopfProj := rfl

theorem isStarProjection_Fproj : IsStarProjection Fproj :=
  isStarProjection_hopfProj.one_sub

/-- `F` has rank two. -/
theorem trace_Fproj : Matrix.trace Fproj = 2 := by
  rw [Fproj_def, Matrix.trace_sub, Matrix.trace_one, trace_hopfProj, Fintype.card_fin]
  norm_num

theorem Fproj_mul_hopfCol : Fproj * hopfCol = 0 := by
  rw [Fproj_def, Matrix.sub_mul, Matrix.one_mul, hopfProj_def, Matrix.mul_assoc,
    hopfCol_conjTranspose_mul, Matrix.mul_one, sub_self]

theorem hopfCol_conjTranspose_mul_Fproj : hopfColᴴ * Fproj = 0 := by
  have h := congrArg Matrix.conjTranspose Fproj_mul_hopfCol
  rw [Matrix.conjTranspose_mul, conjTranspose_eq_of_isStarProjection isStarProjection_Fproj,
    Matrix.conjTranspose_zero] at h
  exact h

theorem hopfProj_add_Fproj : hopfProj + Fproj = 1 := by
  rw [Fproj_def]
  abel

/-- **`F ⊕ 𝟏 ≅ 𝟏³`**, the cancellation identity of the manuscript's §2, as a
Murray–von Neumann equivalence of projections in `M₄(C(S^5))`.

The implementer is the explicit partial isometry `[[F, x], [0, 0]]`. -/
theorem murrayVonNeumannEquiv_Fproj :
    MurrayVonNeumannEquiv
      (Matrix.fromBlocks Fproj 0 0 (1 : Matrix (Fin 1) (Fin 1) C(↥sphereFive, ℂ)))
      (Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) C(↥sphereFive, ℂ)) 0 0
        (0 : Matrix (Fin 1) (Fin 1) C(↥sphereFive, ℂ))) := by
  refine ⟨Matrix.fromBlocks Fproj hopfCol 0 0, ?_, ?_⟩
  · rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero,
      conjTranspose_eq_of_isStarProjection isStarProjection_Fproj,
      Matrix.mul_zero, add_zero,
      isStarProjection_Fproj.isIdempotentElem.eq, Fproj_mul_hopfCol,
      hopfCol_conjTranspose_mul_Fproj, hopfCol_conjTranspose_mul]
  · have hkey : Fproj * Fproj + hopfCol * hopfColᴴ
        = (1 : Matrix (Fin 3) (Fin 3) C(↥sphereFive, ℂ)) := by
      rw [isStarProjection_Fproj.isIdempotentElem.eq, ← hopfProj_def, Fproj_def]
      abel
    rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero,
      conjTranspose_eq_of_isStarProjection isStarProjection_Fproj,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, hkey]

/-! ### Rank is locally constant -/

/-- A continuous function with values in the natural numbers is locally constant. -/
theorem isLocallyConstant_of_natCast_valued {X : Type*} [TopologicalSpace X] {f : X → ℂ}
    (hf : Continuous f) (h : ∀ x, ∃ k : ℕ, f x = (k : ℂ)) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hnbhd : f ⁻¹' Metric.ball (f x) 1 ∈ nhds x :=
    hf.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ one_pos)
  filter_upwards [hnbhd] with y hy
  obtain ⟨k, hk⟩ := h x
  obtain ⟨l, hl⟩ := h y
  have hdist : ‖f y - f x‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hy
  rw [hk, hl] at hdist ⊢
  have hcast : ((l : ℂ) - (k : ℂ)) = (((l : ℝ) - (k : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hdist
  have habs := abs_lt.mp hdist
  have hlk : (l : ℤ) = (k : ℤ) := by
    have h1 : (l : ℤ) - (k : ℤ) < 1 := by
      have : ((l : ℤ) : ℝ) - ((k : ℤ) : ℝ) < 1 := by push_cast; linarith [habs.2]
      exact_mod_cast this
    have h2 : (-1 : ℤ) < (l : ℤ) - (k : ℤ) := by
      have : (-1 : ℝ) < ((l : ℤ) : ℝ) - ((k : ℤ) : ℝ) := by push_cast; linarith [habs.1]
      exact_mod_cast this
    omega
  have hlk' : l = k := by exact_mod_cast hlk
  rw [hlk']

/-- **The rank of a projection-valued function is locally constant.**

Its rank at a point is the trace of the evaluated matrix, which is a natural number
(`STW59.exists_natCast_trace`) and depends continuously on the point. -/
theorem isLocallyConstant_trace {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι C(X, ℂ)} (h : IsStarProjection M) :
    IsLocallyConstant fun x => (Matrix.trace M) x := by
  refine isLocallyConstant_of_natCast_valued (Matrix.trace M).continuous fun x => ?_
  obtain ⟨m, hm⟩ := exists_natCast_trace (isStarProjection_matEval h x)
  exact ⟨m, by rw [← trace_matEval, hm]⟩

end

end STW59
end GroupApproximation
