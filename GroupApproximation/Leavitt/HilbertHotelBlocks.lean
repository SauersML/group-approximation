import GroupApproximation.Leavitt.Leavitt
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.FinCases

/-!
# The Hilbert-hotel block frames of a binary Leavitt family

Fix a ring `R` carrying a binary Leavitt family `L` (`LeavittFamily R`), write
`p = s₀r₀` and `q = s₁r₁` for its two range idempotents, and fix the corner
width `m = 4`.  This file builds the `2m = 8` frame of the Hilbert-hotel
construction, presented as `2 × 2` matrices of `4 × 4` blocks, and proves the
four block-algebra identities the construction runs on:

* `p + q = 1`, `p * q = 0`, `r₁ * q * s₁ = 1` (the Leavitt input);
* the branch-map block matrix `U = !![s₀·I, s₁r₀·I; 0, r₁·I]` is invertible,
  with inverse `V = !![r₀·I, 0; s₀r₁·I, s₁·I]`;
* **compression**: `U · diag(g, I) · V = diag(s₀ g r₀ + q·I, I)`, so conjugation
  by `U` carries the first-block elementary subgroup into the corner `pRp`;
* **moved centralizer**: `U · diag(I, h) · V = diag(p·I + q·h, h)` whenever the
  entries of the mark `h` are central — the hypothesis the 2026-08-21 audit
  added, and which the `𝔽₂`-valued marks used downstream satisfy.

The block frame is `M₂(M₄(R))`; `Matrix.compRingEquiv` and
`Matrix.reindexRingEquiv` transport every identity to the flat `8 × 8` frame
`M₈(R)`, which is done at the end of the file.

The `4m = 16` frame, the defect computation and the saturation chain live in
`GroupApproximation.Leavitt.HilbertHotelSaturation`.
-/

namespace GroupApproximation
namespace HilbertHotel

variable {R : Type*} [Ring R]

/-! ### Scalar blocks

`Matrix.scalar κ a` is the block `a·I`.  Everything the block algebra needs is
that scalar blocks are a ring homomorphic image of `R`, that they multiply an
arbitrary block entrywise on either side, and that a scalar block sandwich
collapses when the middle block has central entries. -/

section Scalar

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem scalar_mul_mul_scalar (a b : R) (g : Matrix κ κ R) :
    Matrix.scalar κ a * g * Matrix.scalar κ b = Matrix.of fun i j => a * g i j * b := by
  ext i j
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]

/-- A scalar sandwich around a block with central entries collapses to a single
scalar factor.  This is the exact point at which the 2026-08-21 audit's
hypothesis sharpening enters. -/
theorem scalar_move (a b : R) (g : Matrix κ κ R)
    (hc : ∀ i j, ∀ x : R, g i j * x = x * g i j) :
    Matrix.scalar κ a * g * Matrix.scalar κ b = Matrix.scalar κ (a * b) * g := by
  rw [scalar_mul_mul_scalar]
  ext i j
  simp only [Matrix.of_apply, Matrix.scalar_apply, Matrix.diagonal_mul]
  rw [mul_assoc, hc i j b, ← mul_assoc]

theorem scalar_mul_single (a x : R) (i j : κ) :
    Matrix.scalar κ a * Matrix.single i j x = Matrix.single i j (a * x) := by
  ext k l
  simp only [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.single_apply]
  split_ifs
  · rfl
  · exact mul_zero a

theorem scalar_mul_single_mul_scalar (a b x : R) (i j : κ) :
    Matrix.scalar κ a * Matrix.single i j x * Matrix.scalar κ b
      = Matrix.single i j (a * x * b) := by
  rw [scalar_mul_mul_scalar]
  ext k l
  simp only [Matrix.of_apply, Matrix.single_apply]
  split_ifs
  · rfl
  · rw [mul_zero, zero_mul]

end Scalar

/-! ### The Leavitt input

`p := s₀r₀` and `q := s₁r₁` are `LeavittFamily.p0` and `LeavittFamily.p1`; the
three relations below are already available in `Leavitt.lean` and are recorded
here only under the names the Hilbert-hotel note uses. -/

section Idempotents

variable (L : LeavittFamily R)

/-- `p + q = 1`. -/
theorem p_add_q : L.p0 + L.p1 = 1 := L.p0_add_p1

/-- `p * q = 0`. -/
theorem p_mul_q : L.p0 * L.p1 = 0 := L.p0_mul_p1

/-- **Fullness of the complementary idempotent**: `r₁ q s₁ = 1`.  This is what
converts the single defect into every elementary generator. -/
theorem r1_mul_q_mul_s1 : L.t1 * L.p1 * L.s1 = 1 := by
  rw [L.t1_mul_p1, L.t1_s1]

/-- The complementary idempotent is nonzero in every nontrivial ring carrying a
binary Leavitt family: `r₁ q s₁ = 1` would otherwise read `0 = 1`. -/
theorem q_ne_zero [Nontrivial R] : L.p1 ≠ 0 := by
  intro h
  have h1 : (1 : R) = 0 := by
    rw [← r1_mul_q_mul_s1 L, h, mul_zero, zero_mul]
  exact one_ne_zero h1

/-! ### Auxiliary scalar identities of the branch map -/

theorem s1r0_mul_s0r1 : L.s1 * L.t0 * (L.s0 * L.t1) = L.p1 := by
  have h : L.s1 * L.t0 * (L.s0 * L.t1) = L.s1 * (L.t0 * L.s0 * L.t1) := by
    simp only [mul_assoc]
  rw [h, L.t0_s0, one_mul]
  rfl

theorem s1r0_mul_s1 : L.s1 * L.t0 * L.s1 = 0 := by
  rw [mul_assoc, L.t0_s1, mul_zero]

theorem r1_mul_s0r1 : L.t1 * (L.s0 * L.t1) = 0 := by
  rw [← mul_assoc, L.t1_s0, zero_mul]

theorem r0_mul_s1r0 : L.t0 * (L.s1 * L.t0) = 0 := by
  rw [← mul_assoc, L.t0_s1, zero_mul]

theorem s0r1_mul_s0 : L.s0 * L.t1 * L.s0 = 0 := by
  rw [mul_assoc, L.t1_s0, mul_zero]

theorem s0r1_mul_s1r0 : L.s0 * L.t1 * (L.s1 * L.t0) = L.p0 := by
  have h : L.s0 * L.t1 * (L.s1 * L.t0) = L.s0 * (L.t1 * L.s1 * L.t0) := by
    simp only [mul_assoc]
  rw [h, L.t1_s1, one_mul]
  rfl

end Idempotents

/-! ### The `2m = 8` frame

`U` and `V` are the branch-map block matrix and its inverse, written as `2 × 2`
matrices of `4 × 4` scalar blocks. -/

section Frame8

variable (L : LeavittFamily R)

/-- `U = !![s₀·I, s₁r₀·I; 0, r₁·I]`, the branch-map block matrix at `m = 4`. -/
def U8 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) R) :=
  !![Matrix.scalar (Fin 4) L.s0, Matrix.scalar (Fin 4) (L.s1 * L.t0);
     0, Matrix.scalar (Fin 4) L.t1]

/-- `V = !![r₀·I, 0; s₀r₁·I, s₁·I]`, the two-sided inverse of `U8`. -/
def V8 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) R) :=
  !![Matrix.scalar (Fin 4) L.t0, 0;
     Matrix.scalar (Fin 4) (L.s0 * L.t1), Matrix.scalar (Fin 4) L.s1]

theorem U8_mul_V8 : U8 L * V8 L = 1 := by
  have e00 : Matrix.scalar (Fin 4) L.s0 * Matrix.scalar (Fin 4) L.t0
      + Matrix.scalar (Fin 4) (L.s1 * L.t0) * Matrix.scalar (Fin 4) (L.s0 * L.t1)
      = (1 : Matrix (Fin 4) (Fin 4) R) := by
    rw [← map_mul, ← map_mul, ← map_add, ← map_one (Matrix.scalar (Fin 4) (α := R))]
    exact congrArg _ (by rw [s1r0_mul_s0r1]; exact L.sum_range)
  have e01 : Matrix.scalar (Fin 4) L.s0 * (0 : Matrix (Fin 4) (Fin 4) R)
      + Matrix.scalar (Fin 4) (L.s1 * L.t0) * Matrix.scalar (Fin 4) L.s1
      = (0 : Matrix (Fin 4) (Fin 4) R) := by
    rw [mul_zero, zero_add, ← map_mul, ← map_zero (Matrix.scalar (Fin 4) (α := R))]
    exact congrArg _ (s1r0_mul_s1 L)
  have e10 : (0 : Matrix (Fin 4) (Fin 4) R) * Matrix.scalar (Fin 4) L.t0
      + Matrix.scalar (Fin 4) L.t1 * Matrix.scalar (Fin 4) (L.s0 * L.t1)
      = (0 : Matrix (Fin 4) (Fin 4) R) := by
    rw [zero_mul, zero_add, ← map_mul, ← map_zero (Matrix.scalar (Fin 4) (α := R))]
    exact congrArg _ (r1_mul_s0r1 L)
  have e11 : (0 : Matrix (Fin 4) (Fin 4) R) * (0 : Matrix (Fin 4) (Fin 4) R)
      + Matrix.scalar (Fin 4) L.t1 * Matrix.scalar (Fin 4) L.s1
      = (1 : Matrix (Fin 4) (Fin 4) R) := by
    rw [zero_mul, zero_add, ← map_mul, ← map_one (Matrix.scalar (Fin 4) (α := R))]
    exact congrArg _ L.t1_s1
  unfold U8 V8
  rw [Matrix.mul_fin_two, e00, e01, e10, e11, Matrix.one_fin_two]

theorem V8_mul_U8 : V8 L * U8 L = 1 := by
  have e00 : Matrix.scalar (Fin 4) L.t0 * Matrix.scalar (Fin 4) L.s0
      + (0 : Matrix (Fin 4) (Fin 4) R) * (0 : Matrix (Fin 4) (Fin 4) R)
      = (1 : Matrix (Fin 4) (Fin 4) R) := by
    rw [zero_mul, add_zero, ← map_mul, ← map_one (Matrix.scalar (Fin 4) (α := R))]
    exact congrArg _ L.t0_s0
  have e01 : Matrix.scalar (Fin 4) L.t0 * Matrix.scalar (Fin 4) (L.s1 * L.t0)
      + (0 : Matrix (Fin 4) (Fin 4) R) * Matrix.scalar (Fin 4) L.t1
      = (0 : Matrix (Fin 4) (Fin 4) R) := by
    rw [zero_mul, add_zero, ← map_mul, ← map_zero (Matrix.scalar (Fin 4) (α := R))]
    exact congrArg _ (r0_mul_s1r0 L)
  have e10 : Matrix.scalar (Fin 4) (L.s0 * L.t1) * Matrix.scalar (Fin 4) L.s0
      + Matrix.scalar (Fin 4) L.s1 * (0 : Matrix (Fin 4) (Fin 4) R)
      = (0 : Matrix (Fin 4) (Fin 4) R) := by
    rw [mul_zero, add_zero, ← map_mul, ← map_zero (Matrix.scalar (Fin 4) (α := R))]
    exact congrArg _ (s0r1_mul_s0 L)
  have e11 : Matrix.scalar (Fin 4) (L.s0 * L.t1) * Matrix.scalar (Fin 4) (L.s1 * L.t0)
      + Matrix.scalar (Fin 4) L.s1 * Matrix.scalar (Fin 4) L.t1
      = (1 : Matrix (Fin 4) (Fin 4) R) := by
    rw [← map_mul, ← map_mul, ← map_add, ← map_one (Matrix.scalar (Fin 4) (α := R))]
    exact congrArg _ (by rw [s0r1_mul_s1r0]; exact L.sum_range)
  unfold V8 U8
  rw [Matrix.mul_fin_two, e00, e01, e10, e11, Matrix.one_fin_two]

/-- `U` as a unit of the `8`-frame. -/
def U8unit : (Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) R))ˣ where
  val := U8 L
  inv := V8 L
  val_inv := U8_mul_V8 L
  inv_val := V8_mul_U8 L

@[simp] theorem U8unit_val : (U8unit L : Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) R))
    = U8 L := rfl

@[simp] theorem U8unit_inv_val : Units.val (U8unit L)⁻¹ = V8 L := rfl

/-! #### Compression -/

theorem U8_mul_blockDiag (g : Matrix (Fin 4) (Fin 4) R) :
    U8 L * !![g, 0; 0, 1]
      = !![Matrix.scalar (Fin 4) L.s0 * g, Matrix.scalar (Fin 4) (L.s1 * L.t0);
           0, Matrix.scalar (Fin 4) L.t1] := by
  unfold U8
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **Compression.**  Conjugation by the branch-map block matrix carries the
first-block copy of `M₄(R)` into the corner: `U · diag(g, I) · V` is
`diag(s₀ g r₀ + q·I, I)`, whose first block has all entries in `s₀Rr₀`. -/
theorem compression (g : Matrix (Fin 4) (Fin 4) R) :
    U8 L * !![g, 0; 0, 1] * V8 L
      = !![Matrix.scalar (Fin 4) L.s0 * g * Matrix.scalar (Fin 4) L.t0
             + Matrix.scalar (Fin 4) L.p1, 0; 0, 1] := by
  have e01 : Matrix.scalar (Fin 4) L.s0 * g * (0 : Matrix (Fin 4) (Fin 4) R)
      + Matrix.scalar (Fin 4) (L.s1 * L.t0) * Matrix.scalar (Fin 4) L.s1
      = (0 : Matrix (Fin 4) (Fin 4) R) := by
    rw [mul_zero, zero_add, ← map_mul, ← map_zero (Matrix.scalar (Fin 4) (α := R))]
    exact congrArg _ (s1r0_mul_s1 L)
  have e10 : (0 : Matrix (Fin 4) (Fin 4) R) * Matrix.scalar (Fin 4) L.t0
      + Matrix.scalar (Fin 4) L.t1 * Matrix.scalar (Fin 4) (L.s0 * L.t1)
      = (0 : Matrix (Fin 4) (Fin 4) R) := by
    rw [zero_mul, zero_add, ← map_mul, ← map_zero (Matrix.scalar (Fin 4) (α := R))]
    exact congrArg _ (r1_mul_s0r1 L)
  have e11 : (0 : Matrix (Fin 4) (Fin 4) R) * (0 : Matrix (Fin 4) (Fin 4) R)
      + Matrix.scalar (Fin 4) L.t1 * Matrix.scalar (Fin 4) L.s1
      = (1 : Matrix (Fin 4) (Fin 4) R) := by
    rw [zero_mul, zero_add, ← map_mul, ← map_one (Matrix.scalar (Fin 4) (α := R))]
    exact congrArg _ L.t1_s1
  have e00 : Matrix.scalar (Fin 4) (L.s1 * L.t0) * Matrix.scalar (Fin 4) (L.s0 * L.t1)
      = Matrix.scalar (Fin 4) L.p1 := by
    rw [← map_mul]
    exact congrArg _ (s1r0_mul_s0r1 L)
  rw [U8_mul_blockDiag]
  unfold V8
  rw [Matrix.mul_fin_two, e00, e01, e10, e11]

/-- The compression on a single elementary generator: `1 + a·E_{ij}` in the first
block becomes `1 + (s₀ a r₀)·E_{ij}`. -/
theorem compression_elementary (a : R) (i j : Fin 4) :
    U8 L * !![1 + Matrix.single i j a, 0; 0, 1] * V8 L
      = !![1 + Matrix.single i j (L.s0 * a * L.t0), 0; 0, 1] := by
  have key : Matrix.scalar (Fin 4) L.s0 * (1 + Matrix.single i j a)
        * Matrix.scalar (Fin 4) L.t0 + Matrix.scalar (Fin 4) L.p1
      = 1 + Matrix.single i j (L.s0 * a * L.t0) := by
    rw [mul_add, mul_one, add_mul, scalar_mul_single_mul_scalar,
      ← map_mul (Matrix.scalar (Fin 4) (α := R)), add_assoc,
      add_comm (Matrix.single i j (L.s0 * a * L.t0)), ← add_assoc,
      ← map_add (Matrix.scalar (Fin 4) (α := R)) (L.s0 * L.t0) L.p1]
    rw [show L.s0 * L.t0 + L.p1 = 1 from L.p0_add_p1, map_one]
  rw [compression, key]

/-! #### The moved centralizer -/

theorem U8_mul_blockMark (h : Matrix (Fin 4) (Fin 4) R) :
    U8 L * !![1, 0; 0, h]
      = !![Matrix.scalar (Fin 4) L.s0, Matrix.scalar (Fin 4) (L.s1 * L.t0) * h;
           0, Matrix.scalar (Fin 4) L.t1 * h] := by
  unfold U8
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **The moved centralizer**, with the centrality hypothesis explicit.  If every
entry of the mark `h` is central then `U · diag(I, h) · V = diag(p·I + q·h, h)`:
the transported mark picks up the complementary idempotent `q` on the first
block.  Without centrality the first block is only `s₁r₀ h s₀r₁`, which does not
collapse. -/
theorem movedCentralizer (h : Matrix (Fin 4) (Fin 4) R)
    (hc : ∀ i j, ∀ x : R, h i j * x = x * h i j) :
    U8 L * !![1, 0; 0, h] * V8 L
      = !![Matrix.scalar (Fin 4) L.p0 + Matrix.scalar (Fin 4) L.p1 * h, 0; 0, h] := by
  have e00 : Matrix.scalar (Fin 4) L.s0 * Matrix.scalar (Fin 4) L.t0
      + Matrix.scalar (Fin 4) (L.s1 * L.t0) * h * Matrix.scalar (Fin 4) (L.s0 * L.t1)
      = Matrix.scalar (Fin 4) L.p0 + Matrix.scalar (Fin 4) L.p1 * h := by
    rw [scalar_move _ _ h hc, ← map_mul (Matrix.scalar (Fin 4) (α := R)), s1r0_mul_s0r1]
    rfl
  have e01 : Matrix.scalar (Fin 4) L.s0 * (0 : Matrix (Fin 4) (Fin 4) R)
      + Matrix.scalar (Fin 4) (L.s1 * L.t0) * h * Matrix.scalar (Fin 4) L.s1
      = (0 : Matrix (Fin 4) (Fin 4) R) := by
    rw [mul_zero, zero_add, scalar_move _ _ h hc, s1r0_mul_s1,
      map_zero (Matrix.scalar (Fin 4) (α := R)), zero_mul]
  have e10 : (0 : Matrix (Fin 4) (Fin 4) R) * Matrix.scalar (Fin 4) L.t0
      + Matrix.scalar (Fin 4) L.t1 * h * Matrix.scalar (Fin 4) (L.s0 * L.t1)
      = (0 : Matrix (Fin 4) (Fin 4) R) := by
    rw [zero_mul, zero_add, scalar_move _ _ h hc, r1_mul_s0r1,
      map_zero (Matrix.scalar (Fin 4) (α := R)), zero_mul]
  have e11 : (0 : Matrix (Fin 4) (Fin 4) R) * (0 : Matrix (Fin 4) (Fin 4) R)
      + Matrix.scalar (Fin 4) L.t1 * h * Matrix.scalar (Fin 4) L.s1
      = h := by
    rw [zero_mul, zero_add, scalar_move _ _ h hc, L.t1_s1,
      map_one (Matrix.scalar (Fin 4) (α := R)), one_mul]
  rw [U8_mul_blockMark]
  unfold V8
  rw [Matrix.mul_fin_two, e00, e01, e10, e11]

end Frame8

/-! ### The distinguished mark and the defect -/

section Mark

variable (L : LeavittFamily R)

/-- The distinguished `𝔽₂`-valued mark `h = 1 + E₁₂` of the corner width.  Its
entries are `0` and `1`, hence central in every ring. -/
def mark (S : Type*) [Ring S] : Matrix (Fin 4) (Fin 4) S := 1 + Matrix.single 0 1 1

theorem mark_central (i j : Fin 4) (x : R) :
    mark R i j * x = x * mark R i j := by
  unfold mark
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs
  · rw [add_mul, mul_add, one_mul, mul_one]
  · rw [add_zero, one_mul, mul_one]
  · rw [zero_add, one_mul, mul_one]
  · rw [add_zero, zero_mul, mul_zero]

/-- **The defect appears.**  Transporting the commuting second-block mark
`diag(I, 1 + E₁₂)` by the branch-map block matrix leaves the mark alone in the
second block and deposits the elementary matrix `1 + q·E₁₂` in the first: this
single element is the compression defect the whole construction turns on. -/
theorem movedCentralizer_mark :
    U8 L * !![1, 0; 0, mark R] * V8 L
      = !![1 + Matrix.single 0 1 L.p1, 0; 0, mark R] := by
  have key : Matrix.scalar (Fin 4) L.p0 + Matrix.scalar (Fin 4) L.p1 * mark R
      = 1 + Matrix.single (0 : Fin 4) 1 L.p1 := by
    unfold mark
    rw [mul_add, mul_one, scalar_mul_single, mul_one, ← add_assoc,
      ← map_add (Matrix.scalar (Fin 4) (α := R)) L.p0 L.p1, L.p0_add_p1, map_one]
  rw [movedCentralizer L (mark R) (mark_central), key]

end Mark

/-! ### The flat `8 × 8` frame

`M₂(M₄(R)) ≅ M_{Fin 2 × Fin 4}(R) ≅ M₈(R)`.  Both isomorphisms are ring
isomorphisms, so `U · V = V · U = 1` transports verbatim. -/

section Flat

variable (L : LeavittFamily R)

/-- The branch-map block matrix in the flat `Fin 2 × Fin 4` frame. -/
def U8flat : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) R :=
  Matrix.compRingEquiv (Fin 2) (Fin 4) R (U8 L)

/-- Its inverse in the flat `Fin 2 × Fin 4` frame. -/
def V8flat : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) R :=
  Matrix.compRingEquiv (Fin 2) (Fin 4) R (V8 L)

theorem U8flat_mul_V8flat : U8flat L * V8flat L = 1 := by
  rw [U8flat, V8flat, ← map_mul, U8_mul_V8, map_one]

theorem V8flat_mul_U8flat : V8flat L * U8flat L = 1 := by
  rw [U8flat, V8flat, ← map_mul, V8_mul_U8, map_one]

/-- The index identification `Fin 2 × Fin 4 ≃ Fin 8`. -/
def frame8 : Fin 2 × Fin 4 ≃ Fin 8 := finProdFinEquiv

/-- `U` as an honest `8 × 8` matrix. -/
def U8fin : Matrix (Fin 8) (Fin 8) R :=
  Matrix.reindexRingEquiv R frame8 (U8flat L)

/-- `V` as an honest `8 × 8` matrix. -/
def V8fin : Matrix (Fin 8) (Fin 8) R :=
  Matrix.reindexRingEquiv R frame8 (V8flat L)

theorem U8fin_mul_V8fin : U8fin L * V8fin L = 1 := by
  rw [U8fin, V8fin, ← map_mul, U8flat_mul_V8flat, map_one]

theorem V8fin_mul_U8fin : V8fin L * U8fin L = 1 := by
  rw [U8fin, V8fin, ← map_mul, V8flat_mul_U8flat, map_one]

/-- `U ∈ GL₈(R)`: the Hilbert-hotel branch map is a unit of the `2m` frame. -/
def U8finUnit : (Matrix (Fin 8) (Fin 8) R)ˣ where
  val := U8fin L
  inv := V8fin L
  val_inv := U8fin_mul_V8fin L
  inv_val := V8fin_mul_U8fin L

end Flat

end HilbertHotel
end GroupApproximation
