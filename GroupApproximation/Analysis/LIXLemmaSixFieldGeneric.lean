import GroupApproximation.Analysis.LIXLemmaSixField
import GroupApproximation.Analysis.LIXGenericEquator

/-!
# The corner, its ambient, and the extension, generic in the rank

Lane `sp-tower` of the STW Problem LIX strengthening programme
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.1).

`Analysis/LIXLemmaSixField.lean` §3 builds the bridge Corollary 4 runs across: the
null-homotopy lives in the corner cut out by `E = 𝟏² ⊕ P` inside `M_{Fin 2 ⊕ H}`, while
the unitary field it produces has to live in `M_{Fin 3 ⊕ H}`, and `ext3` is the extension
that crosses between them.  This file re-authors that section with the rank `n` as a
parameter: the corner is `𝟏^n ⊕ P` inside `M_{Fin n ⊕ H}`, the ambient is
`M_{Fin (n+1) ⊕ H}`, and `Gen.extAmb n` is the extension.

Everything here is already abstract in the block bundle `P : Y → Matrix HI HI ℂ` and in
the base `Y`, so the rank is the *only* thing being generalised — which is why the section
ports cleanly and why `§5` can check each rank-two name against its `n = 2` instance.

## What the isometry needs, and where it comes from

The extension is conjugation by `jIncl = incl ⊕ 𝟏_H`, and it works because `incl` is an
isometry with the pole as cokernel:

```text
inclᴴ * incl = 1 ,        incl * inclᴴ = 1 − e e ᴴ ,      e = ePole n .
```

Both are `Analysis/LIXGenericEquator.lean`'s `Gen.incl_conjTranspose_mul` and
`Gen.incl_mul_conjTranspose`, already proved at every rank for `sp-powers`.  So this port
needed no new geometry at all; it is the rank-two argument with `Fin 2 ↦ Fin n`,
`Fin 3 ↦ Fin (n+1)` and `e₃ ↦ ePole n`.

## Why this survives the renormalised generator

The lead's redesign replaces the endpoint witness `u` by `ũ := Aᴴ u` and substitutes the
frames.  It changes **what** unitary of the corner is extended; it does not change the
corner, the ambient, the isometry between them, or any identity below.  So this layer is
needed in either form.

## Main results

* `Gen.cornerE`, `Gen.bigE`, `Gen.bigF`, `Gen.jIncl`, `Gen.extAmb` — the four blocks and
  the extension, at rank `n`.
* `Gen.IsCornerUnit` — a unitary of the corner.
* `Gen.extAmb_conjTranspose_mul_self`, `Gen.extAmb_mul_conjTranspose` — **the extension of
  a corner unitary is unitary**, at every rank.
* `Gen.extAmb_mul`, `Gen.extAmb_cornerE`, `Gen.extAmb_fromBlocks` — it is multiplicative,
  unital, and block-diagonal.
* `§5` — the rank-two bridges.
-/

namespace GroupApproximation
namespace LIX

open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace Gen

/-! ## 1. The corner, the ambient, and the isometry between them -/

variable {HI : Type*} [Fintype HI] [DecidableEq HI]
variable {Y : Type*} [TopologicalSpace Y]

/-- `E = 𝟏^n ⊕ P`, the unit of the corner the null-homotopy lives in. -/
def cornerE (n : ℕ) (P : Y → Matrix HI HI ℂ) (y : Y) :
    Matrix (Fin n ⊕ HI) (Fin n ⊕ HI) ℂ :=
  Matrix.fromBlocks 1 0 0 (P y)

/-- `(𝟏^{n+1} − e eᴴ) ⊕ P`, the constant complement, `e = ePole n`. -/
def bigE (n : ℕ) (P : Y → Matrix HI HI ℂ) (y : Y) :
    Matrix (Fin (n + 1) ⊕ HI) (Fin (n + 1) ⊕ HI) ℂ :=
  Matrix.fromBlocks (1 - rk1 (ePole n) (ePole n)) 0 0 (P y)

/-- `(𝟏^{n+1} − x xᴴ) ⊕ P`, the moving complement. -/
def bigF (n : ℕ) (P : Y → Matrix HI HI ℂ) (x : Fin (n + 1) → ℂ) (y : Y) :
    Matrix (Fin (n + 1) ⊕ HI) (Fin (n + 1) ⊕ HI) ℂ :=
  Matrix.fromBlocks (1 - rk1 x x) 0 0 (P y)

/-- The isometry `ℂ^n ⊕ ℂ^H → ℂ^{n+1} ⊕ ℂ^H`. -/
def jIncl (n : ℕ) (HI : Type*) [Fintype HI] [DecidableEq HI] :
    Matrix (Fin (n + 1) ⊕ HI) (Fin n ⊕ HI) ℂ :=
  Matrix.fromBlocks (incl n) 0 0 1

/-- **The extension of a corner unitary to a unitary of the ambient.** -/
def extAmb (n : ℕ) (P : Y → Matrix HI HI ℂ) (y : Y)
    (A : Matrix (Fin n ⊕ HI) (Fin n ⊕ HI) ℂ) :
    Matrix (Fin (n + 1) ⊕ HI) (Fin (n + 1) ⊕ HI) ℂ :=
  jIncl n HI * A * (jIncl n HI)ᴴ + (1 - bigE n P y)

/-- A unitary of the corner cut out by `E`. -/
structure IsCornerUnit (n : ℕ) (P : Y → Matrix HI HI ℂ) (y : Y)
    (A : Matrix (Fin n ⊕ HI) (Fin n ⊕ HI) ℂ) : Prop where
  /-- `AᴴA` is the unit of the corner. -/
  star_mul : Aᴴ * A = cornerE n P y
  /-- `AAᴴ` is the unit of the corner. -/
  mul_star : A * Aᴴ = cornerE n P y

variable {n : ℕ} {P : Y → Matrix HI HI ℂ} {y : Y}
variable {A B : Matrix (Fin n ⊕ HI) (Fin n ⊕ HI) ℂ}

/-! ## 2. The two projections -/

theorem continuous_cornerE (n : ℕ) (hP : Continuous P) :
    Continuous fun y => cornerE n P y := by
  simp only [cornerE]
  exact Continuous.matrix_fromBlocks continuous_const continuous_const continuous_const hP

theorem continuous_bigE (n : ℕ) (hP : Continuous P) : Continuous fun y => bigE n P y := by
  simp only [bigE]
  exact Continuous.matrix_fromBlocks continuous_const continuous_const continuous_const hP

theorem conjTranspose_cornerE (h : (P y)ᴴ = P y) : (cornerE n P y)ᴴ = cornerE n P y := by
  simp only [cornerE, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one, h]

theorem cornerE_mul_self (h : P y * P y = P y) :
    cornerE n P y * cornerE n P y = cornerE n P y := by
  simp only [cornerE, fromBlocks_diag_mul_rect, Matrix.one_mul, h]

theorem conjTranspose_bigE (h : (P y)ᴴ = P y) : (bigE n P y)ᴴ = bigE n P y := by
  simp only [bigE, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero, h,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, rk1_conjTranspose]

theorem rk1_ePole_mul_self (n : ℕ) :
    rk1 (ePole n) (ePole n) * rk1 (ePole n) (ePole n) = rk1 (ePole n) (ePole n) := by
  rw [rk1_mul, unit_ePole, one_smul]

theorem bigE_mul_self (h : P y * P y = P y) : bigE n P y * bigE n P y = bigE n P y := by
  simp only [bigE, fromBlocks_diag_mul_rect, h, one_sub_mul_one_sub (rk1_ePole_mul_self n)]

/-! ## 3. Conjugation by the isometry -/

theorem jIncl_conjTranspose_mul (n : ℕ) : (jIncl n HI)ᴴ * jIncl n HI = 1 := by
  simp only [jIncl, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one, fromBlocks_diag_mul_rect, incl_conjTranspose_mul, Matrix.one_mul,
    Matrix.fromBlocks_one]

theorem jIncl_mul_cornerE : jIncl n HI * cornerE n P y * (jIncl n HI)ᴴ = bigE n P y := by
  simp only [jIncl, cornerE, bigE, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one, fromBlocks_diag_mul_rect, Matrix.one_mul, Matrix.mul_one,
    incl_mul_conjTranspose]

/-- Conjugation by the isometry is multiplicative. -/
theorem jconj_mul (A B : Matrix (Fin n ⊕ HI) (Fin n ⊕ HI) ℂ) :
    jIncl n HI * A * (jIncl n HI)ᴴ * (jIncl n HI * B * (jIncl n HI)ᴴ)
      = jIncl n HI * (A * B) * (jIncl n HI)ᴴ := by
  calc jIncl n HI * A * (jIncl n HI)ᴴ * (jIncl n HI * B * (jIncl n HI)ᴴ)
      = jIncl n HI * (A * ((jIncl n HI)ᴴ * jIncl n HI) * (B * (jIncl n HI)ᴴ)) := by
        simp only [Matrix.mul_assoc]
    _ = jIncl n HI * (A * B * (jIncl n HI)ᴴ) := by
        rw [jIncl_conjTranspose_mul, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = jIncl n HI * (A * B) * (jIncl n HI)ᴴ := by simp only [Matrix.mul_assoc]

theorem jconj_conjTranspose (A : Matrix (Fin n ⊕ HI) (Fin n ⊕ HI) ℂ) :
    (jIncl n HI * A * (jIncl n HI)ᴴ)ᴴ = jIncl n HI * Aᴴ * (jIncl n HI)ᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

namespace IsCornerUnit

theorem cornerE_mul (h : IsCornerUnit n P y A) (hP : P y * P y = P y) :
    cornerE n P y * A = A :=
  proj_mul_of_partial h.star_mul h.mul_star (cornerE_mul_self hP)

theorem mul_cornerE (h : IsCornerUnit n P y A) (hP : P y * P y = P y) :
    A * cornerE n P y = A :=
  mul_proj_of_partial h.star_mul h.mul_star (cornerE_mul_self hP)

theorem mul' (hA : IsCornerUnit n P y A) (hB : IsCornerUnit n P y B) (hP : P y * P y = P y) :
    IsCornerUnit n P y (A * B) where
  star_mul := by
    rw [Matrix.conjTranspose_mul]
    calc Bᴴ * Aᴴ * (A * B) = Bᴴ * (Aᴴ * A) * B := by simp only [Matrix.mul_assoc]
      _ = cornerE n P y := by
            rw [hA.star_mul, Matrix.mul_assoc, hB.cornerE_mul hP, hB.star_mul]
  mul_star := by
    rw [Matrix.conjTranspose_mul]
    calc A * B * (Bᴴ * Aᴴ) = A * (B * Bᴴ) * Aᴴ := by simp only [Matrix.mul_assoc]
      _ = cornerE n P y := by rw [hB.mul_star, hA.mul_cornerE hP, hA.mul_star]

end IsCornerUnit

theorem jconj_mul_bigE (hA : IsCornerUnit n P y A) (hP : P y * P y = P y) :
    jIncl n HI * A * (jIncl n HI)ᴴ * bigE n P y = jIncl n HI * A * (jIncl n HI)ᴴ := by
  rw [← jIncl_mul_cornerE (P := P) (y := y), jconj_mul, hA.mul_cornerE hP]

theorem bigE_mul_jconj (hA : IsCornerUnit n P y A) (hP : P y * P y = P y) :
    bigE n P y * (jIncl n HI * A * (jIncl n HI)ᴴ) = jIncl n HI * A * (jIncl n HI)ᴴ := by
  rw [← jIncl_mul_cornerE (P := P) (y := y), jconj_mul, hA.cornerE_mul hP]

theorem jconj_conjTranspose_mul_self (hA : IsCornerUnit n P y A) :
    (jIncl n HI * A * (jIncl n HI)ᴴ)ᴴ * (jIncl n HI * A * (jIncl n HI)ᴴ) = bigE n P y := by
  rw [jconj_conjTranspose, jconj_mul, hA.star_mul, jIncl_mul_cornerE]

theorem jconj_mul_conjTranspose (hA : IsCornerUnit n P y A) :
    jIncl n HI * A * (jIncl n HI)ᴴ * (jIncl n HI * A * (jIncl n HI)ᴴ)ᴴ = bigE n P y := by
  rw [jconj_conjTranspose, jconj_mul, hA.mul_star, jIncl_mul_cornerE]

/-! ## 4. The extension is unitary, multiplicative and unital -/

theorem extAmb_conjTranspose_mul_self (hA : IsCornerUnit n P y A) (hP : P y * P y = P y)
    (hPs : (P y)ᴴ = P y) : (extAmb n P y A)ᴴ * extAmb n P y A = 1 :=
  conjTranspose_mul_self_add_compl (conjTranspose_bigE hPs) (bigE_mul_self hP)
    (jconj_conjTranspose_mul_self hA) (bigE_mul_jconj hA hP)

theorem extAmb_mul_conjTranspose (hA : IsCornerUnit n P y A) (hP : P y * P y = P y)
    (hPs : (P y)ᴴ = P y) : extAmb n P y A * (extAmb n P y A)ᴴ = 1 :=
  mul_conjTranspose_add_compl (conjTranspose_bigE hPs) (bigE_mul_self hP)
    (jconj_mul_conjTranspose hA) (jconj_mul_bigE hA hP)

theorem extAmb_comm_bigE (hA : IsCornerUnit n P y A) (hP : P y * P y = P y) :
    extAmb n P y A * bigE n P y = bigE n P y * extAmb n P y A := by
  have h1 : extAmb n P y A * bigE n P y = jIncl n HI * A * (jIncl n HI)ᴴ := by
    rw [extAmb, Matrix.add_mul, jconj_mul_bigE hA hP, Matrix.sub_mul, Matrix.one_mul,
      bigE_mul_self hP, sub_self, add_zero]
  have h2 : bigE n P y * extAmb n P y A = jIncl n HI * A * (jIncl n HI)ᴴ := by
    rw [extAmb, Matrix.mul_add, bigE_mul_jconj hA hP, Matrix.mul_sub, Matrix.mul_one,
      bigE_mul_self hP, sub_self, add_zero]
  rw [h1, h2]

theorem extAmb_mul (hA : IsCornerUnit n P y A) (hB : IsCornerUnit n P y B)
    (hP : P y * P y = P y) :
    extAmb n P y (A * B) = extAmb n P y A * extAmb n P y B := by
  have e1 : jIncl n HI * A * (jIncl n HI)ᴴ * (1 - bigE n P y) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, jconj_mul_bigE hA hP, sub_self]
  have e2 : (1 - bigE n P y) * (jIncl n HI * B * (jIncl n HI)ᴴ) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, bigE_mul_jconj hB hP, sub_self]
  rw [extAmb, extAmb, extAmb, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, jconj_mul, e1, e2,
    one_sub_mul_one_sub (bigE_mul_self hP)]
  abel

theorem extAmb_cornerE : extAmb n P y (cornerE n P y) = 1 := by
  rw [extAmb, jIncl_mul_cornerE]
  abel

/-- `extAmb` in blocks. -/
theorem extAmb_fromBlocks (A' : Matrix (Fin n) (Fin n) ℂ) (D : Matrix HI HI ℂ) :
    extAmb n P y (Matrix.fromBlocks A' 0 0 D)
      = Matrix.fromBlocks (incl n * A' * (incl n)ᴴ + rk1 (ePole n) (ePole n)) 0 0
          (D + (1 - P y)) := by
  have hone : (1 : Matrix (Fin (n + 1) ⊕ HI) (Fin (n + 1) ⊕ HI) ℂ)
      = Matrix.fromBlocks (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 0 0
          (1 : Matrix HI HI ℂ) := Matrix.fromBlocks_one.symm
  rw [extAmb, jIncl, hone, bigE, fromBlocks_sub]
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero, Matrix.conjTranspose_one,
    fromBlocks_diag_mul_rect, Matrix.one_mul, Matrix.mul_one, Matrix.fromBlocks_add, sub_self,
    sub_sub_cancel, add_zero]

theorem continuous_jconj (n : ℕ) :
    Continuous fun A : Matrix (Fin n ⊕ HI) (Fin n ⊕ HI) ℂ =>
      jIncl n HI * A * (jIncl n HI)ᴴ :=
  (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem continuousAt_extAmb {Z : Type*} [TopologicalSpace Z] (n : ℕ) (hP : Continuous P)
    {Af : Z → Matrix (Fin n ⊕ HI) (Fin n ⊕ HI) ℂ} {yf : Z → Y} {z : Z}
    (hA : ContinuousAt Af z) (hy : ContinuousAt yf z) :
    ContinuousAt (fun z => extAmb n P (yf z) (Af z)) z := by
  have hb : ContinuousAt
      (fun z => (1 : Matrix (Fin (n + 1) ⊕ HI) (Fin (n + 1) ⊕ HI) ℂ) - bigE n P (yf z)) z :=
    continuousAt_const.sub ((continuous_bigE n hP).continuousAt.comp hy)
  have ha : ContinuousAt (fun z => jIncl n HI * Af z * (jIncl n HI)ᴴ) z :=
    (continuous_jconj (HI := HI) n).continuousAt.comp hA
  simp only [extAmb]
  exact ha.add hb

end Gen

/-! ## 5. The rank-two bridges

Each rank-two name of `LIXLemmaSixField.lean` §3 is its own `n = 2` instance, definitionally:
`Fin 2` is `Fin 2`, `Fin 3` is `Fin (2 + 1)`, `e₃` is `ePole 2` and `incl` is `incl 2`.  As
in `CharClass/LIXShapeGeneric.lean`, no `cast` and no `Equiv` stands between the fixed-rank
layer and the generic one. -/

/-- The two spellings of the isometry agree, but **not** definitionally: the rank-two
`incl` branches on `(i : ℕ) = (j : ℕ)` through `Nat.decEq`, and `Gen.incl` branches on
`i = j.castSucc` through `instDecidableEqFin`.  The values match at every entry; the
`Decidable` instances do not, and `rfl` sees the instances.  Six closed cases. -/
theorem incl_eq_gen : (incl : Matrix (Fin 3) (Fin 2) ℂ) = Gen.incl 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

variable {HI : Type*} [Fintype HI] [DecidableEq HI]
variable {Y : Type*} [TopologicalSpace Y] {P : Y → Matrix HI HI ℂ} {y : Y}

theorem cornerE_eq_gen : cornerE P y = Gen.cornerE 2 P y := rfl

theorem bigE_eq_gen : bigE P y = Gen.bigE 2 P y := rfl

theorem bigF_eq_gen (x : Fin 3 → ℂ) : bigF P x y = Gen.bigF 2 P x y := rfl

theorem jIncl_eq_gen : jIncl HI = Gen.jIncl 2 HI := by
  rw [jIncl, Gen.jIncl, incl_eq_gen]

theorem ext3_eq_gen (A : Matrix (Fin 2 ⊕ HI) (Fin 2 ⊕ HI) ℂ) :
    ext3 P y A = Gen.extAmb 2 P y A := by
  rw [ext3, Gen.extAmb, jIncl_eq_gen, bigE_eq_gen]

theorem isCornerUnit_iff_gen (A : Matrix (Fin 2 ⊕ HI) (Fin 2 ⊕ HI) ℂ) :
    IsCornerUnit P y A ↔ Gen.IsCornerUnit 2 P y A :=
  ⟨fun h => ⟨h.star_mul, h.mul_star⟩, fun h => ⟨h.star_mul, h.mul_star⟩⟩

end

end LIX
end GroupApproximation
