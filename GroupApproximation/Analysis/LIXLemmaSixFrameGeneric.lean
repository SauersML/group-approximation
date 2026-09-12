import GroupApproximation.Analysis.LIXLemmaSixFieldGeneric

/-!
# The padded frames, generic in the rank

Lane `sp-tower` of the STW Problem LIX strengthening programme
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.1).

§4 of `Analysis/LIXLemmaSixField.lean` at rank `n`.  A frame of the trivial block is padded
by the identity on `H` to act on the ambient `ℂ^{n+1} ⊕ ℂ^H`, and a unitary of `H` is
padded the other way; `frameAmb_conj_bigE` is the one statement with content, that
conjugating the constant complement by a frame gives the moving complement.

## Why the two paddings are separate definitions

`frameAmb n HI σ = σ ⊕ 𝟏_H` and `coframeAmb n HI D = 𝟏^{n+1} ⊕ D` commute
(`frameAmb_comm_coframeAmb`), which is the only reason the seam argument can move the
frame past the `H`-block without knowing anything about either.  Keeping them as two
one-line definitions rather than one general `fromBlocks` is what makes that commutation a
`simp only` on four block products.

## What this layer does and does not fix

It fixes the *padding*, not the frame.  `σ` is a parameter throughout, so the
renormalised-generator redesign — which substitutes the hemisphere frames gauged by `A`
and, for the `k`-th power, pulls them back along `Σψ_k` — changes only what is fed to
`frameAmb n HI`, and no statement below moves.  That is the reason this section can be
ported before the `k`-th-power frames exist.

## Main results

* `Gen.frameAmb`, `Gen.coframeAmb` — the two paddings at rank `n`.
* `Gen.frameAmb_star_mul`, `Gen.frameAmb_mul_star`, `Gen.coframeAmb_mul_star` — padding
  preserves unitarity.
* `Gen.frameAmb_comm_coframeAmb` — the two paddings commute.
* `Gen.frameAmb_conj_bigE` — **a frame carries the constant complement to the moving one**,
  at every rank.
* `§2` — the rank-two bridges, both `rfl`.
-/

namespace GroupApproximation
namespace LIX

open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace Gen

/-! ## 1. The two paddings -/

variable {HI : Type*} [Fintype HI] [DecidableEq HI]
variable {Y : Type*} [TopologicalSpace Y]

/-- `σ ⊕ 𝟏_H`. -/
def frameAmb (n : ℕ) (HI : Type*) [Fintype HI] [DecidableEq HI]
    (σ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Fin (n + 1) ⊕ HI) (Fin (n + 1) ⊕ HI) ℂ :=
  Matrix.fromBlocks σ 0 0 1

/-- `𝟏^{n+1} ⊕ D`. -/
def coframeAmb (n : ℕ) (HI : Type*) [Fintype HI] [DecidableEq HI] (D : Matrix HI HI ℂ) :
    Matrix (Fin (n + 1) ⊕ HI) (Fin (n + 1) ⊕ HI) ℂ :=
  Matrix.fromBlocks 1 0 0 D

variable {n : ℕ} {σ τ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {D : Matrix HI HI ℂ}

theorem frameAmb_conjTranspose : (frameAmb n HI σ)ᴴ = frameAmb n HI σᴴ := by
  simp only [frameAmb, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one]

theorem coframeAmb_conjTranspose : (coframeAmb n HI D)ᴴ = coframeAmb n HI Dᴴ := by
  simp only [coframeAmb, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one]

theorem frameAmb_mul : frameAmb n HI σ * frameAmb n HI τ = frameAmb n HI (σ * τ) := by
  simp only [frameAmb, fromBlocks_diag_mul_rect, Matrix.one_mul]

theorem frameAmb_one : frameAmb n HI (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 1 := by
  simp only [frameAmb, Matrix.fromBlocks_one]

theorem frameAmb_star_mul (h : σᴴ * σ = 1) : (frameAmb n HI σ)ᴴ * frameAmb n HI σ = 1 := by
  rw [frameAmb_conjTranspose, frameAmb_mul, h, frameAmb_one]

theorem frameAmb_mul_star (h : σ * σᴴ = 1) : frameAmb n HI σ * (frameAmb n HI σ)ᴴ = 1 := by
  rw [frameAmb_conjTranspose, frameAmb_mul, h, frameAmb_one]

theorem coframeAmb_mul_star (h : D * Dᴴ = 1) :
    coframeAmb n HI D * (coframeAmb n HI D)ᴴ = 1 := by
  rw [coframeAmb_conjTranspose, coframeAmb, coframeAmb, fromBlocks_diag_mul_rect,
    Matrix.one_mul, h, Matrix.fromBlocks_one]

theorem frameAmb_comm_coframeAmb :
    frameAmb n HI σ * coframeAmb n HI D = coframeAmb n HI D * frameAmb n HI σ := by
  simp only [frameAmb, coframeAmb, fromBlocks_diag_mul_rect, Matrix.one_mul, Matrix.mul_one]

/-! ## 2. A frame carries the constant complement to the moving one -/

/-- **The one statement with content.**  If `σ` carries `pole^⊥` to `x^⊥` in the trivial
block, then its padding carries `bigE` to `bigF`.  `σ` is a parameter, so the
renormalised-generator redesign changes what is fed in here and nothing else. -/
theorem frameAmb_conj_bigE {x : Fin (n + 1) → ℂ} (P : Y → Matrix HI HI ℂ) (y : Y)
    (hσ : σ * (1 - rk1 (ePole n) (ePole n)) * σᴴ = 1 - rk1 x x) :
    frameAmb n HI σ * bigE n P y * (frameAmb n HI σ)ᴴ = bigF n P x y := by
  simp only [frameAmb, bigE, bigF, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one, fromBlocks_diag_mul_rect, Matrix.one_mul, Matrix.mul_one, hσ]

theorem continuous_frameAmb :
    Continuous fun σ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => frameAmb n HI σ := by
  simp only [frameAmb]
  exact Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
    continuous_const

end Gen

/-! ## 3. The rank-two bridges

Both `rfl`: the paddings are `Matrix.fromBlocks` applied to the same four blocks, with no
decidable branch anywhere, and `Fin 3` is `Fin (2 + 1)`. -/

variable {HI : Type*} [Fintype HI] [DecidableEq HI]

theorem frame3_eq_gen (σ : Matrix (Fin 3) (Fin 3) ℂ) :
    frame3 HI σ = Gen.frameAmb 2 HI σ := rfl

theorem coframe3_eq_gen (D : Matrix HI HI ℂ) :
    coframe3 HI D = Gen.coframeAmb 2 HI D := rfl

end

end LIX
end GroupApproximation
