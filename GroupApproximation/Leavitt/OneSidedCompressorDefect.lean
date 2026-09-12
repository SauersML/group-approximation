import GroupApproximation.Leavitt.OneSidedCompressor
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefect

/-!
# The centralizer element and the printed defect at rank four

`non_mf_groups_exist.tex`, Section `sec:one-sided-inverses`, the end of the
proof of Theorem `thm:full-defect-ring`:

> The element `c = [e₄₁(e), e₁₄(t)] = diag(1,1,1,1+et)` is computed in the block
> on coordinates `(1,4)` using `te = 0`, and a diagonal matrix of this shape
> commutes with every `diag(A,1)`, so `c ∈ C_G(L)`.  Since `t³e = 0`, the matrix
> `uc` differs from `u` only in its last column … and multiplying by `u⁻¹` gives
> `ucu⁻¹ = e₁₂(e)`.  For `ℓ = e₂₃(1)` the Steinberg relation
> `[e₁₂(e), e₂₃(1)] = e₁₃(e)` gives `d = [ucu⁻¹, ℓ] = e₁₃(e) ∈ 𝔇_G(L)`.

Coordinates are 0-indexed here, so the printed `c` is `centralMark P`, the
printed `ℓ = e₂₃(1)` is `printedEll R`, and the printed defect
`d = e₁₃(e)` is `printedDefectRoot P`.  The conclusion
`printedDefectRoot_mem_printedDefect` is the membership
`d ∈ 𝔇_G(L)` in the manuscript's own defect subgroup
`Manuscript.OneSidedMFRadical.printedDefect`.

Everything is over an arbitrary unital ring and uses only `t s = 1`.  Turning
this membership into `𝔇_G(L) = ⊤` needs the ideal condition on `e`, and is in
`GroupApproximation.Leavitt.FullIdempotentNormalGeneration`.
-/

namespace GroupApproximation
namespace OneSidedCompressor

open scoped commutatorElement

universe u

variable {R : Type u} [Ring R]

/-! ### The three core index inequalities used by name -/

theorem zeroNeOne : (0 : Fin 3) ≠ 1 := by decide

theorem zeroNeTwo : (0 : Fin 3) ≠ 2 := by decide

theorem oneNeTwo : (1 : Fin 3) ≠ 2 := by decide

/-! ### The printed centralizer element -/

/-- The printed centralizer mark `c = [e₄₁(e), e₁₄(t)]`, written out as the
four transvections of the commutator. -/
def centralMark (P : OneSidedInverse R) : elementaryGroup (Fin 4) R :=
  elementaryRoot lastIdx (coreIdx 0) (last_ne_coreIdx 0) P.e *
    elementaryRoot (coreIdx 0) lastIdx (coreIdx_ne_last 0) P.t *
      elementaryRoot lastIdx (coreIdx 0) (last_ne_coreIdx 0) (-P.e) *
        elementaryRoot (coreIdx 0) lastIdx (coreIdx_ne_last 0) (-P.t)

/-- The printed centralizer mark is the printed commutator. -/
theorem centralMark_eq_commutator (P : OneSidedInverse R) :
    centralMark P =
      ⁅elementaryRoot lastIdx (coreIdx 0) (last_ne_coreIdx 0) P.e,
        elementaryRoot (coreIdx 0) lastIdx (coreIdx_ne_last 0) P.t⁆ := by
  rw [commutatorElement_def, centralMark, elementaryRoot_neg, elementaryRoot_neg]

/-- The printed value `c = diag(1,1,1,1+et)`. -/
def centralMarkMatrix (P : OneSidedInverse R) : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1 + P.e * P.t]

@[simp] theorem centralMark_val (P : OneSidedInverse R) :
    (↑(↑(centralMark P) : (Matrix (Fin 4) (Fin 4) R)ˣ) :
        Matrix (Fin 4) (Fin 4) R)
      = centralMarkMatrix P := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [centralMark, centralMarkMatrix, elementaryRoot, elementaryUnit,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ, coreIdx, lastIdx,
      mul_add, add_mul, mul_assoc]

/-- A diagonal matrix of this shape commutes with every core root. -/
theorem centralMark_commute_coreRoot (P : OneSidedInverse R)
    (i j : Fin 3) (hij : i ≠ j) (a : R) :
    Commute (centralMark P)
      (elementaryRoot (coreIdx i) (coreIdx j) (coreIdx_injective.ne hij) a) := by
  apply Subtype.ext
  apply Units.ext
  ext r c
  fin_cases i <;> fin_cases j
  all_goals try simp at hij
  all_goals fin_cases r <;> fin_cases c
  all_goals
    simp [elementaryRoot, elementaryUnit, centralMarkMatrix, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ, coreIdx, mul_add, add_mul,
      mul_assoc]

/-- **The printed conclusion `c ∈ C_G(L)`.** -/
theorem centralMark_commute_core (P : OneSidedInverse R) :
    ∀ g ∈ core R, Commute (centralMark P) g := by
  intro g hg
  rw [core] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      exact centralMark_commute_coreRoot P i j hij a
  | one => exact Commute.one_right _
  | mul x y _ _ hx hy => exact hx.mul_right hy
  | inv x _ hx => exact hx.inv_right

/-! ### Conjugating the mark into the core -/

/-- `uc` differs from `u` only in its last column: the multiplicative form of
the printed `ucu⁻¹ = e₁₂(e)`. -/
theorem compressor_mul_centralMark (P : OneSidedInverse R) :
    compressor P * centralMark P =
      elementaryRoot (coreIdx 0) (coreIdx 1) (coreIdx_injective.ne zeroNeOne) P.e *
        compressor P := by
  apply Subtype.ext
  apply Units.ext
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [elementaryRoot, elementaryUnit, compressorMatrix, centralMarkMatrix,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ, coreIdx,
      mul_add, add_mul, mul_assoc]

/-- **The printed identity `ucu⁻¹ = e₁₂(e)`.** -/
theorem compressor_conj_centralMark (P : OneSidedInverse R) :
    compressor P * centralMark P * (compressor P)⁻¹ =
      elementaryRoot (coreIdx 0) (coreIdx 1) (coreIdx_injective.ne zeroNeOne) P.e := by
  rw [compressor_mul_centralMark]
  group

/-! ### The printed defect -/

/-- The printed core element `ℓ = e₂₃(1)`. -/
def printedEll (R : Type u) [Ring R] : elementaryGroup (Fin 4) R :=
  elementaryRoot (coreIdx 1) (coreIdx 2) (coreIdx_injective.ne oneNeTwo) 1

theorem printedEll_mem_core : printedEll R ∈ core R :=
  elementaryRoot_mem_core 1 2 oneNeTwo 1

/-- The printed defect element `d = e₁₃(e)`. -/
def printedDefectRoot (P : OneSidedInverse R) : elementaryGroup (Fin 4) R :=
  elementaryRoot (coreIdx 0) (coreIdx 2) (coreIdx_injective.ne zeroNeTwo) P.e

/-- **The printed Steinberg step `d = [ucu⁻¹, ℓ] = e₁₃(e)`.** -/
theorem defect_eq (P : OneSidedInverse R) :
    ⁅compressor P * centralMark P * (compressor P)⁻¹, printedEll R⁆ =
      printedDefectRoot P := by
  rw [compressor_conj_centralMark, printedEll, printedDefectRoot,
    elementaryRoot_commutator (coreIdx 0) (coreIdx 1) (coreIdx 2)
      (coreIdx_injective.ne zeroNeOne) (coreIdx_injective.ne oneNeTwo)
      (coreIdx_injective.ne zeroNeTwo) P.e 1,
    mul_one]

/-- The compressor is a one-sided compressor of the core in the manuscript's
own sense. -/
theorem compressor_mem_compressionSet (P : OneSidedInverse R) :
    compressor P ∈ compressionSet (core R) :=
  compressor_compresses_core P

/-- **The rank-four milestone.**  `d = e₁₃(e)` lies in the printed defect
`𝔇_G(L)` of `eq:intrinsic-defect`, for every one-sided inverse pair over every
unital ring. -/
theorem printedDefectRoot_mem_printedDefect (P : OneSidedInverse R) :
    printedDefectRoot P ∈
      Manuscript.OneSidedMFRadical.printedDefect (core R) := by
  rw [← defect_eq P]
  exact Manuscript.OneSidedMFRadical.printedDefect_generator_mem (core R)
    (compressor_compresses_core P) (centralMark_commute_core P) printedEll_mem_core

end OneSidedCompressor
end GroupApproximation
