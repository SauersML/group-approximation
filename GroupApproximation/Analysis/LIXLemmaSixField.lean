import GroupApproximation.Analysis.LIXLemmaSixEquator

/-!
# Corollary 4, the analytic half: the unitary field over `S⁵ × Y`

Corollary 4 says that a null-homotopy of the stage unitary `u ⊕ c` produces the
Murray--von Neumann equivalence Lemma 2 denies.
`Analysis/LIXLemmaSixCompare.lean` is the algebraic half: a continuous field of
unitaries conjugating the constant complement onto the moving one *is* the
equivalence.  This file builds that field, and it is the only place where the
topology of `S⁵` is used.

## The construction

Over the northern cap the field is the northern frame `frameNorth e₃ x`, padded by
the identity of the `H` block.  Over the southern cap it is the southern frame,
corrected by the null-homotopy read at the cone coordinates of the point: the
radius `capTime x` and the equatorial direction `dirPt x`.  On the equator
`capTime = 1` and `equatorEmb (dirPt x) = x`, so the correction is the seam
discrepancy itself and the two fields agree; the gluing is `continuous_if_le`.

## Why there is no analysis at the pole

`dirPt` is discontinuous at the south pole, and the usual cure is to present the
cap as a quotient of `[0,1] × S⁴`.  None of that is needed here, because
`capTime x = max 0 (1 + 2 Re x₂)` is *clamped*: it vanishes on the whole collar
`{Re x₂ ≤ -1/2}`, where the correction is therefore the constant `W 0 = 1`,
whatever the direction is.  So the southern field is continuous on the collar
because it is locally the southern frame alone, and continuous off the collar
because `dirPt` is continuous there; those two open sets cover the cap.  No
quotient map, no cone surjectivity, no `arcsin`, and no estimate.

## The extension `ext3`

The homotopy lives in the corner cut out by `E = 𝟏² ⊕ P` inside `M_{Fin 2 ⊕ H}`,
while the field has to be a unitary of `M_{Fin 3 ⊕ H}`.  The isometry
`jIncl = incl ⊕ 𝟏` conjugates the one into the other, and
`ext3 P y A = jIncl A jInclᴴ + (1 - bigE P y)` fills in the orthogonal complement
by the identity.  `ext3` carries corner unitaries to unitaries, is multiplicative
on them, and commutes with `bigE`, which is exactly what the conjugation argument
needs.

## Main results

* `ext3`, `ext3_conjTranspose_mul_self`, `ext3_mul`, `ext3_comm_bigE` — the extension.
* `capTime`, `dirPt` — the cone coordinates, with the clamp.
* `southF_eq_northF` — **the seam**.
* `exists_unitary_field_of_nullHomotopy` — **the analytic half of Corollary 4**.
-/

namespace GroupApproximation
namespace LIX

open scoped Matrix ComplexOrder

set_option linter.unusedSectionVars false

noncomputable section

/-! ## 1. Rectangular block algebra -/

section Blocks

variable {l m n o q r : Type*}

theorem fromBlocks_sub {R : Type*} [Sub R] (A A' : Matrix n l R) (B B' : Matrix n m R)
    (C C' : Matrix o l R) (D D' : Matrix o m R) :
    Matrix.fromBlocks A B C D - Matrix.fromBlocks A' B' C' D'
      = Matrix.fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

/-- Block-diagonal multiplication with rectangular blocks; `STW59.fromBlocks_diag_mul`
is the square case, which the isometry `incl : ℂ² → ℂ³` is not. -/
theorem fromBlocks_diag_mul_rect {R : Type*} [Fintype l] [Fintype m]
    [NonUnitalNonAssocSemiring R] (A : Matrix n l R) (D : Matrix o m R) (A' : Matrix l q R)
    (D' : Matrix m r R) :
    Matrix.fromBlocks A 0 0 D * Matrix.fromBlocks A' 0 0 D'
      = Matrix.fromBlocks (A * A') 0 0 (D * D') := by
  rw [Matrix.fromBlocks_multiply]
  simp

end Blocks

/-! ## 2. Partial isometries -/

section PartialIsometry

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem one_sub_mul_one_sub {q : Matrix n n ℂ} (hq : q * q = q) :
    (1 - q) * (1 - q) = 1 - q := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hq]
  abel

/-- A partial isometry with initial and final projection `q` is fixed by `q`. -/
theorem proj_mul_of_partial {c q : Matrix n n ℂ} (h1 : cᴴ * c = q) (h2 : c * cᴴ = q)
    (hq : q * q = q) : q * c = c := by
  have hqh : qᴴ = q := by
    rw [← h2, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hx : cᴴ * q * c = q := by
    calc cᴴ * q * c = cᴴ * c * (cᴴ * c) := by
          rw [← h2]
          simp only [Matrix.mul_assoc]
      _ = q := by rw [h1, hq]
  have e1 : cᴴ * (q * c) = q := by rw [← Matrix.mul_assoc]; exact hx
  have e2 : cᴴ * q * (q * c) = q := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc cᴴ q q, hq]
    exact hx
  have key : (c - q * c)ᴴ * (c - q * c) = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hqh, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, h1, e1, hx, e2]
    abel
  exact (sub_eq_zero.mp (Matrix.conjTranspose_mul_self_eq_zero.mp key)).symm

theorem mul_proj_of_partial {c q : Matrix n n ℂ} (h1 : cᴴ * c = q) (h2 : c * cᴴ = q)
    (hq : q * q = q) : c * q = c := by
  have hqh : qᴴ = q := by
    rw [← h2, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have h := proj_mul_of_partial (c := cᴴ) (q := q)
    (by rw [Matrix.conjTranspose_conjTranspose]; exact h2)
    (by rw [Matrix.conjTranspose_conjTranspose]; exact h1) hq
  have h' := congrArg Matrix.conjTranspose h
  rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hqh] at h'

/-- **Filling in the complement of a partial isometry gives a unitary.** -/
theorem conjTranspose_mul_self_add_compl {B q : Matrix n n ℂ} (hq : qᴴ = q) (hqq : q * q = q)
    (h1 : Bᴴ * B = q) (h4 : q * B = B) : (B + (1 - q))ᴴ * (B + (1 - q)) = 1 := by
  have hBh : (B + (1 - q))ᴴ = Bᴴ + (1 - q) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hq]
  have hBq : Bᴴ * q = Bᴴ := by
    have h' := congrArg Matrix.conjTranspose h4
    rwa [Matrix.conjTranspose_mul, hq] at h'
  have e1 : Bᴴ * (1 - q) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hBq, sub_self]
  have e2 : (1 - q) * B = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h4, sub_self]
  rw [hBh, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h1, e1, e2,
    one_sub_mul_one_sub hqq]
  abel

theorem mul_conjTranspose_add_compl {B q : Matrix n n ℂ} (hq : qᴴ = q) (hqq : q * q = q)
    (h2 : B * Bᴴ = q) (h3 : B * q = B) : (B + (1 - q)) * (B + (1 - q))ᴴ = 1 := by
  have hBh : (B + (1 - q))ᴴ = Bᴴ + (1 - q) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hq]
  have hqB : q * Bᴴ = Bᴴ := by
    have h' := congrArg Matrix.conjTranspose h3
    rwa [Matrix.conjTranspose_mul, hq] at h'
  have e1 : B * (1 - q) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, h3, sub_self]
  have e2 : (1 - q) * Bᴴ = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hqB, sub_self]
  rw [hBh, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h2, e1, e2,
    one_sub_mul_one_sub hqq]
  abel

theorem mul_star_mul_of_unitary {A B : Matrix n n ℂ} (h1 : Aᴴ * A = 1) (h2 : Bᴴ * B = 1) :
    (A * B)ᴴ * (A * B) = 1 := by
  rw [Matrix.conjTranspose_mul]
  calc Bᴴ * Aᴴ * (A * B) = Bᴴ * (Aᴴ * A) * B := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, h2]

theorem mul_mul_star_of_unitary {A B : Matrix n n ℂ} (h1 : A * Aᴴ = 1) (h2 : B * Bᴴ = 1) :
    (A * B) * (A * B)ᴴ = 1 := by
  rw [Matrix.conjTranspose_mul]
  calc A * B * (Bᴴ * Aᴴ) = A * (B * Bᴴ) * Aᴴ := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h2, Matrix.mul_one, h1]

theorem conj_eq_of_comm {A Q : Matrix n n ℂ} (h1 : A * Aᴴ = 1) (h2 : A * Q = Q * A) :
    A * Q * Aᴴ = Q := by
  rw [h2, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem conjTranspose_comm_of_comm {A Q : Matrix n n ℂ} (hQ : Qᴴ = Q) (h : A * Q = Q * A) :
    Aᴴ * Q = Q * Aᴴ := by
  have h' := congrArg Matrix.conjTranspose h
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQ] at h'
  exact h'.symm

/-- Conjugation of a projection by a product of three unitaries, two of which
commute with it. -/
theorem conj_triple {S T U Q R : Matrix n n ℂ} (hT : T * Tᴴ = 1)
    (hU : U * Uᴴ = 1) (hTQ : T * Q = Q * T) (hUQ : U * Q = Q * U) (hSQ : S * Q * Sᴴ = R) :
    S * T * U * Q * (S * T * U)ᴴ = R := by
  have hVQ : T * U * Q = Q * (T * U) := by
    rw [Matrix.mul_assoc, hUQ, ← Matrix.mul_assoc, hTQ, Matrix.mul_assoc]
  have hV : T * U * (T * U)ᴴ = 1 := mul_mul_star_of_unitary hT hU
  have key : S * (T * U) * Q * (S * (T * U))ᴴ = R := by
    rw [Matrix.conjTranspose_mul]
    calc S * (T * U) * Q * ((T * U)ᴴ * Sᴴ) = S * (T * U * Q * (T * U)ᴴ) * Sᴴ := by
          simp only [Matrix.mul_assoc]
      _ = S * Q * Sᴴ := by rw [conj_eq_of_comm hV hVQ]
      _ = R := hSQ
  calc S * T * U * Q * (S * T * U)ᴴ = S * (T * U) * Q * (S * (T * U))ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = R := key

end PartialIsometry

/-! ## 3. The corner, its ambient, and the extension -/

section Extension

variable {HI : Type*} [Fintype HI] [DecidableEq HI]
variable {Y : Type*} [TopologicalSpace Y]

/-- `E = 𝟏² ⊕ P`, the unit of the corner the null-homotopy lives in. -/
def cornerE (P : Y → Matrix HI HI ℂ) (y : Y) : Matrix (Fin 2 ⊕ HI) (Fin 2 ⊕ HI) ℂ :=
  Matrix.fromBlocks 1 0 0 (P y)

/-- `(𝟏³ − e₃e₃ᴴ) ⊕ P`, the constant complement. -/
def bigE (P : Y → Matrix HI HI ℂ) (y : Y) : Matrix (Fin 3 ⊕ HI) (Fin 3 ⊕ HI) ℂ :=
  Matrix.fromBlocks (1 - rk1 e3 e3) 0 0 (P y)

/-- `(𝟏³ − x xᴴ) ⊕ P`, the moving complement. -/
def bigF (P : Y → Matrix HI HI ℂ) (x : Fin 3 → ℂ) (y : Y) :
    Matrix (Fin 3 ⊕ HI) (Fin 3 ⊕ HI) ℂ :=
  Matrix.fromBlocks (1 - rk1 x x) 0 0 (P y)

/-- The isometry `ℂ² ⊕ ℂ^H → ℂ³ ⊕ ℂ^H`. -/
def jIncl (HI : Type*) [Fintype HI] [DecidableEq HI] :
    Matrix (Fin 3 ⊕ HI) (Fin 2 ⊕ HI) ℂ :=
  Matrix.fromBlocks incl 0 0 1

/-- **The extension of a corner unitary to a unitary of the ambient.** -/
def ext3 (P : Y → Matrix HI HI ℂ) (y : Y) (A : Matrix (Fin 2 ⊕ HI) (Fin 2 ⊕ HI) ℂ) :
    Matrix (Fin 3 ⊕ HI) (Fin 3 ⊕ HI) ℂ :=
  jIncl HI * A * (jIncl HI)ᴴ + (1 - bigE P y)

/-- A unitary of the corner cut out by `E`. -/
structure IsCornerUnit (P : Y → Matrix HI HI ℂ) (y : Y)
    (A : Matrix (Fin 2 ⊕ HI) (Fin 2 ⊕ HI) ℂ) : Prop where
  star_mul : Aᴴ * A = cornerE P y
  mul_star : A * Aᴴ = cornerE P y

variable {P : Y → Matrix HI HI ℂ} {y : Y} {A B : Matrix (Fin 2 ⊕ HI) (Fin 2 ⊕ HI) ℂ}

theorem continuous_cornerE (hP : Continuous P) : Continuous fun y => cornerE P y := by
  simp only [cornerE]
  exact Continuous.matrix_fromBlocks continuous_const continuous_const continuous_const hP

theorem continuous_bigE (hP : Continuous P) : Continuous fun y => bigE P y := by
  simp only [bigE]
  exact Continuous.matrix_fromBlocks continuous_const continuous_const continuous_const hP

theorem conjTranspose_cornerE (h : (P y)ᴴ = P y) : (cornerE P y)ᴴ = cornerE P y := by
  simp only [cornerE, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one, h]

theorem cornerE_mul_self (h : P y * P y = P y) : cornerE P y * cornerE P y = cornerE P y := by
  simp only [cornerE, fromBlocks_diag_mul_rect, Matrix.one_mul, h]

theorem conjTranspose_bigE (h : (P y)ᴴ = P y) : (bigE P y)ᴴ = bigE P y := by
  simp only [bigE, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero, h,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_one, rk1_conjTranspose]

theorem rk1_e3_mul_self : rk1 e3 e3 * rk1 e3 e3 = rk1 e3 e3 := by
  rw [rk1_mul, unit_e3, one_smul]

theorem bigE_mul_self (h : P y * P y = P y) : bigE P y * bigE P y = bigE P y := by
  simp only [bigE, fromBlocks_diag_mul_rect, h, one_sub_mul_one_sub rk1_e3_mul_self]

theorem jIncl_conjTranspose_mul : (jIncl HI)ᴴ * jIncl HI = 1 := by
  simp only [jIncl, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one, fromBlocks_diag_mul_rect, incl_conjTranspose_mul, Matrix.one_mul,
    Matrix.fromBlocks_one]

theorem jIncl_mul_cornerE : jIncl HI * cornerE P y * (jIncl HI)ᴴ = bigE P y := by
  simp only [jIncl, cornerE, bigE, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one, fromBlocks_diag_mul_rect, Matrix.one_mul, Matrix.mul_one,
    incl_mul_conjTranspose]

/-- Conjugation by the isometry is multiplicative. -/
theorem jconj_mul (A B : Matrix (Fin 2 ⊕ HI) (Fin 2 ⊕ HI) ℂ) :
    jIncl HI * A * (jIncl HI)ᴴ * (jIncl HI * B * (jIncl HI)ᴴ)
      = jIncl HI * (A * B) * (jIncl HI)ᴴ := by
  calc jIncl HI * A * (jIncl HI)ᴴ * (jIncl HI * B * (jIncl HI)ᴴ)
      = jIncl HI * (A * ((jIncl HI)ᴴ * jIncl HI) * (B * (jIncl HI)ᴴ)) := by
        simp only [Matrix.mul_assoc]
    _ = jIncl HI * (A * B * (jIncl HI)ᴴ) := by
        rw [jIncl_conjTranspose_mul, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = jIncl HI * (A * B) * (jIncl HI)ᴴ := by simp only [Matrix.mul_assoc]

theorem jconj_conjTranspose (A : Matrix (Fin 2 ⊕ HI) (Fin 2 ⊕ HI) ℂ) :
    (jIncl HI * A * (jIncl HI)ᴴ)ᴴ = jIncl HI * Aᴴ * (jIncl HI)ᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

namespace IsCornerUnit

theorem cornerE_mul (h : IsCornerUnit P y A) (hP : P y * P y = P y) :
    cornerE P y * A = A :=
  proj_mul_of_partial h.star_mul h.mul_star (cornerE_mul_self hP)

theorem mul_cornerE (h : IsCornerUnit P y A) (hP : P y * P y = P y) :
    A * cornerE P y = A :=
  mul_proj_of_partial h.star_mul h.mul_star (cornerE_mul_self hP)

theorem mul' (hA : IsCornerUnit P y A) (hB : IsCornerUnit P y B) (hP : P y * P y = P y) :
    IsCornerUnit P y (A * B) where
  star_mul := by
    rw [Matrix.conjTranspose_mul]
    calc Bᴴ * Aᴴ * (A * B) = Bᴴ * (Aᴴ * A) * B := by simp only [Matrix.mul_assoc]
      _ = cornerE P y := by
            rw [hA.star_mul, Matrix.mul_assoc, hB.cornerE_mul hP, hB.star_mul]
  mul_star := by
    rw [Matrix.conjTranspose_mul]
    calc A * B * (Bᴴ * Aᴴ) = A * (B * Bᴴ) * Aᴴ := by simp only [Matrix.mul_assoc]
      _ = cornerE P y := by rw [hB.mul_star, hA.mul_cornerE hP, hA.mul_star]

end IsCornerUnit

theorem jconj_mul_bigE (hA : IsCornerUnit P y A) (hP : P y * P y = P y) :
    jIncl HI * A * (jIncl HI)ᴴ * bigE P y = jIncl HI * A * (jIncl HI)ᴴ := by
  rw [← jIncl_mul_cornerE (P := P) (y := y), jconj_mul, hA.mul_cornerE hP]

theorem bigE_mul_jconj (hA : IsCornerUnit P y A) (hP : P y * P y = P y) :
    bigE P y * (jIncl HI * A * (jIncl HI)ᴴ) = jIncl HI * A * (jIncl HI)ᴴ := by
  rw [← jIncl_mul_cornerE (P := P) (y := y), jconj_mul, hA.cornerE_mul hP]

theorem jconj_conjTranspose_mul_self (hA : IsCornerUnit P y A) :
    (jIncl HI * A * (jIncl HI)ᴴ)ᴴ * (jIncl HI * A * (jIncl HI)ᴴ) = bigE P y := by
  rw [jconj_conjTranspose, jconj_mul, hA.star_mul, jIncl_mul_cornerE]

theorem jconj_mul_conjTranspose (hA : IsCornerUnit P y A) :
    jIncl HI * A * (jIncl HI)ᴴ * (jIncl HI * A * (jIncl HI)ᴴ)ᴴ = bigE P y := by
  rw [jconj_conjTranspose, jconj_mul, hA.mul_star, jIncl_mul_cornerE]

theorem ext3_conjTranspose_mul_self (hA : IsCornerUnit P y A) (hP : P y * P y = P y)
    (hPs : (P y)ᴴ = P y) : (ext3 P y A)ᴴ * ext3 P y A = 1 :=
  conjTranspose_mul_self_add_compl (conjTranspose_bigE hPs) (bigE_mul_self hP)
    (jconj_conjTranspose_mul_self hA) (bigE_mul_jconj hA hP)

theorem ext3_mul_conjTranspose (hA : IsCornerUnit P y A) (hP : P y * P y = P y)
    (hPs : (P y)ᴴ = P y) : ext3 P y A * (ext3 P y A)ᴴ = 1 :=
  mul_conjTranspose_add_compl (conjTranspose_bigE hPs) (bigE_mul_self hP)
    (jconj_mul_conjTranspose hA) (jconj_mul_bigE hA hP)

theorem ext3_comm_bigE (hA : IsCornerUnit P y A) (hP : P y * P y = P y) :
    ext3 P y A * bigE P y = bigE P y * ext3 P y A := by
  have h1 : ext3 P y A * bigE P y = jIncl HI * A * (jIncl HI)ᴴ := by
    rw [ext3, Matrix.add_mul, jconj_mul_bigE hA hP, Matrix.sub_mul, Matrix.one_mul,
      bigE_mul_self hP, sub_self, add_zero]
  have h2 : bigE P y * ext3 P y A = jIncl HI * A * (jIncl HI)ᴴ := by
    rw [ext3, Matrix.mul_add, bigE_mul_jconj hA hP, Matrix.mul_sub, Matrix.mul_one,
      bigE_mul_self hP, sub_self, add_zero]
  rw [h1, h2]

theorem ext3_mul (hA : IsCornerUnit P y A) (hB : IsCornerUnit P y B) (hP : P y * P y = P y) :
    ext3 P y (A * B) = ext3 P y A * ext3 P y B := by
  have e1 : jIncl HI * A * (jIncl HI)ᴴ * (1 - bigE P y) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, jconj_mul_bigE hA hP, sub_self]
  have e2 : (1 - bigE P y) * (jIncl HI * B * (jIncl HI)ᴴ) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, bigE_mul_jconj hB hP, sub_self]
  rw [ext3, ext3, ext3, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, jconj_mul, e1, e2,
    one_sub_mul_one_sub (bigE_mul_self hP)]
  abel

theorem ext3_cornerE : ext3 P y (cornerE P y) = 1 := by
  rw [ext3, jIncl_mul_cornerE]
  abel

/-- `ext3` in blocks. -/
theorem ext3_fromBlocks (A' : Matrix (Fin 2) (Fin 2) ℂ) (D : Matrix HI HI ℂ) :
    ext3 P y (Matrix.fromBlocks A' 0 0 D)
      = Matrix.fromBlocks (incl * A' * inclᴴ + rk1 e3 e3) 0 0 (D + (1 - P y)) := by
  have hone : (1 : Matrix (Fin 3 ⊕ HI) (Fin 3 ⊕ HI) ℂ)
      = Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) ℂ) 0 0
          (1 : Matrix HI HI ℂ) := Matrix.fromBlocks_one.symm
  rw [ext3, jIncl, hone, bigE, fromBlocks_sub]
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero, Matrix.conjTranspose_one,
    fromBlocks_diag_mul_rect, Matrix.one_mul, Matrix.mul_one, Matrix.fromBlocks_add, sub_self,
    sub_sub_cancel, add_zero]

theorem continuous_jconj :
    Continuous fun A : Matrix (Fin 2 ⊕ HI) (Fin 2 ⊕ HI) ℂ =>
      jIncl HI * A * (jIncl HI)ᴴ :=
  (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem continuousAt_ext3 {Z : Type*} [TopologicalSpace Z] (hP : Continuous P)
    {Af : Z → Matrix (Fin 2 ⊕ HI) (Fin 2 ⊕ HI) ℂ} {yf : Z → Y} {z : Z}
    (hA : ContinuousAt Af z) (hy : ContinuousAt yf z) :
    ContinuousAt (fun z => ext3 P (yf z) (Af z)) z := by
  have hb : ContinuousAt
      (fun z => (1 : Matrix (Fin 3 ⊕ HI) (Fin 3 ⊕ HI) ℂ) - bigE P (yf z)) z :=
    continuousAt_const.sub ((continuous_bigE hP).continuousAt.comp hy)
  have ha : ContinuousAt (fun z => jIncl HI * Af z * (jIncl HI)ᴴ) z :=
    (continuous_jconj (HI := HI)).continuousAt.comp hA
  simp only [ext3]
  exact ha.add hb

end Extension

/-! ## 4. The padded frames -/

section Frames

variable {HI : Type*} [Fintype HI] [DecidableEq HI]
variable {Y : Type*} [TopologicalSpace Y]

/-- `σ ⊕ 𝟏_H`. -/
def frame3 (HI : Type*) [Fintype HI] [DecidableEq HI] (σ : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin 3 ⊕ HI) (Fin 3 ⊕ HI) ℂ :=
  Matrix.fromBlocks σ 0 0 1

/-- `𝟏³ ⊕ D`. -/
def coframe3 (HI : Type*) [Fintype HI] [DecidableEq HI] (D : Matrix HI HI ℂ) :
    Matrix (Fin 3 ⊕ HI) (Fin 3 ⊕ HI) ℂ :=
  Matrix.fromBlocks 1 0 0 D

variable {σ τ : Matrix (Fin 3) (Fin 3) ℂ} {D : Matrix HI HI ℂ}

theorem frame3_conjTranspose : (frame3 HI σ)ᴴ = frame3 HI σᴴ := by
  simp only [frame3, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one]

theorem coframe3_conjTranspose : (coframe3 HI D)ᴴ = coframe3 HI Dᴴ := by
  simp only [coframe3, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one]

theorem frame3_mul : frame3 HI σ * frame3 HI τ = frame3 HI (σ * τ) := by
  simp only [frame3, fromBlocks_diag_mul_rect, Matrix.one_mul]

theorem frame3_one : frame3 HI (1 : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
  simp only [frame3, Matrix.fromBlocks_one]

theorem frame3_star_mul (h : σᴴ * σ = 1) : (frame3 HI σ)ᴴ * frame3 HI σ = 1 := by
  rw [frame3_conjTranspose, frame3_mul, h, frame3_one]

theorem frame3_mul_star (h : σ * σᴴ = 1) : frame3 HI σ * (frame3 HI σ)ᴴ = 1 := by
  rw [frame3_conjTranspose, frame3_mul, h, frame3_one]

theorem coframe3_mul_star (h : D * Dᴴ = 1) :
    coframe3 HI D * (coframe3 HI D)ᴴ = 1 := by
  rw [coframe3_conjTranspose, coframe3, coframe3, fromBlocks_diag_mul_rect, Matrix.one_mul, h,
    Matrix.fromBlocks_one]

theorem frame3_comm_coframe3 :
    frame3 HI σ * coframe3 HI D = coframe3 HI D * frame3 HI σ := by
  simp only [frame3, coframe3, fromBlocks_diag_mul_rect, Matrix.one_mul, Matrix.mul_one]

theorem frame3_conj_bigE {x : Fin 3 → ℂ} (P : Y → Matrix HI HI ℂ) (y : Y)
    (hσ : σ * (1 - rk1 e3 e3) * σᴴ = 1 - rk1 x x) :
    frame3 HI σ * bigE P y * (frame3 HI σ)ᴴ = bigF P x y := by
  simp only [frame3, bigE, bigF, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_one, fromBlocks_diag_mul_rect, Matrix.one_mul, Matrix.mul_one, hσ]

theorem continuous_frame3 :
    Continuous fun σ : Matrix (Fin 3) (Fin 3) ℂ => frame3 HI σ := by
  simp only [frame3]
  exact Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
    continuous_const

end Frames

/-! ## 5. The seam discrepancy, undone -/

/-- The southern frame corrected by the generator is the northern frame: this is
the whole content of the clutching comparison. -/
theorem frameSouth_mul_genU_conjTranspose {x : Fin 3 → ℂ}
    (hx : x ∈ STW59.unitVectors (Fin 3)) (hS : x 2 ≠ 1) :
    frameSouth e3 x * (genU x)ᴴ = frameNorth e3 x := by
  have h1 : (genU x)ᴴ = (frameSouth e3 x)ᴴ * frameNorth e3 x := by
    rw [genU, seamGen, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [h1, ← Matrix.mul_assoc,
    frameSouth_mul_conjTranspose unit_e3 (isFrameDatum_neg_e3 hx hS), Matrix.one_mul]

/-- The compression of the generator, filled back in. -/
theorem incl_genU2_add {x : Fin 3 → ℂ} (hx : x ∈ STW59.unitVectors (Fin 3))
    (hN : x 2 ≠ -1) (hS : x 2 ≠ 1) :
    incl * genU2 x * inclᴴ + rk1 e3 e3 = genU x := by
  have h1 : incl * genU2 x * inclᴴ = incl * inclᴴ * genU x * (incl * inclᴴ) := by
    rw [genU2]
    simp only [Matrix.mul_assoc]
  rw [h1, incl_mul_conjTranspose]
  have h2 : (1 - rk1 e3 e3) * genU x * (1 - rk1 e3 e3)
      = (1 - rk1 e3 e3) * ((1 - rk1 e3 e3) * genU x) := by
    rw [Matrix.mul_assoc, ← genU_comm_compl hx hN hS]
  rw [h2, ← Matrix.mul_assoc, one_sub_mul_one_sub rk1_e3_mul_self, Matrix.sub_mul,
    Matrix.one_mul, rk1_e3_mul_genU hx hN hS]
  abel

/-! ## 6. The cone coordinates of the southern cap -/

section Cone

/-- The clamped cone radius: `1` on the equator, `0` on the collar
`{Re x₂ ≤ -1/2}` around the south pole. -/
def capTime (x : ↥STW59.sphereFive) : ℝ := max 0 (1 + 2 * ((x : Fin 3 → ℂ) 2).re)

theorem continuous_capTime : Continuous capTime :=
  continuous_const.max (continuous_const.add (continuous_const.mul continuous_capHeight))

theorem capTime_eq_one {x : ↥STW59.sphereFive} (h : ((x : Fin 3 → ℂ) 2).re = 0) :
    capTime x = 1 := by
  simp only [capTime, h]
  norm_num

theorem capTime_eq_zero {x : ↥STW59.sphereFive} (h : ((x : Fin 3 → ℂ) 2).re ≤ -(1 / 2)) :
    capTime x = 0 := by
  simp only [capTime]
  exact max_eq_left (by linarith)

theorem norm_sq_equatorInv {x : Fin 3 → ℂ} (hx : x ∈ STW59.unitVectors (Fin 3)) :
    ‖equatorInv x‖ ^ 2 = 1 - (x 2).re ^ 2 := by
  have hsum : (∑ i, ‖x i‖ ^ 2 : ℝ) = 1 := hx
  rw [Fin.sum_univ_three] at hsum
  have e0 : ‖x 0‖ ^ 2 = (x 0).re ^ 2 + (x 0).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have e1 : ‖x 1‖ ^ 2 = (x 1).re ^ 2 + (x 1).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have e2 : ‖x 2‖ ^ 2 = (x 2).re ^ 2 + (x 2).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [e0, e1, e2] at hsum
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_five]
  simp only [equatorInv_zero, equatorInv_one, equatorInv_two, equatorInv_three, equatorInv_four,
    Real.norm_eq_abs, sq_abs]
  linarith

theorem equatorInv_ne_zero {x : Fin 3 → ℂ} (hx : x ∈ STW59.unitVectors (Fin 3))
    (h : (x 2).re ^ 2 < 1) : equatorInv x ≠ 0 := by
  intro hc
  have h2 := norm_sq_equatorInv hx
  rw [hc, norm_zero] at h2
  nlinarith

theorem continuous_equatorInv : Continuous equatorInv := by
  have h : Continuous fun x : Fin 3 → ℂ =>
      (![(x 0).re, (x 0).im, (x 1).re, (x 1).im, (x 2).im] : Fin 5 → ℝ) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · show Continuous fun x : Fin 3 → ℂ => (x 0).re
      exact Complex.continuous_re.comp (continuous_apply 0)
    · show Continuous fun x : Fin 3 → ℂ => (x 0).im
      exact Complex.continuous_im.comp (continuous_apply 0)
    · show Continuous fun x : Fin 3 → ℂ => (x 1).re
      exact Complex.continuous_re.comp (continuous_apply 1)
    · show Continuous fun x : Fin 3 → ℂ => (x 1).im
      exact Complex.continuous_im.comp (continuous_apply 1)
    · show Continuous fun x : Fin 3 → ℂ => (x 2).im
      exact Complex.continuous_im.comp (continuous_apply 2)
  exact (PiLp.continuous_toLp 2 fun _ : Fin 5 => ℝ).comp h

open scoped Classical in
/-- The equatorial direction of a point of `S⁵`, away from the two poles. -/
def dirPt (x : ↥STW59.sphereFive) : ↥STW59.sphereFour :=
  if h : equatorInv ((x : Fin 3 → ℂ)) = 0 then Classical.arbitrary _
  else ⟨‖equatorInv ((x : Fin 3 → ℂ))‖⁻¹ • equatorInv ((x : Fin 3 → ℂ)),
    mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm h)⟩

theorem coe_dirPt_of_ne {x : ↥STW59.sphereFive} (h : equatorInv ((x : Fin 3 → ℂ)) ≠ 0) :
    (dirPt x : EuclideanSpace ℝ (Fin 5))
      = ‖equatorInv ((x : Fin 3 → ℂ))‖⁻¹ • equatorInv ((x : Fin 3 → ℂ)) := by
  simp only [dirPt, dif_neg h]

/-- Continuity into a subtype, at a point. -/
theorem continuousAt_subtype_mk {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    {pr : Z → Prop} {f : X → Subtype pr} {x : X}
    (hf : ContinuousAt (fun x => ((f x : Z))) x) : ContinuousAt f x := by
  rw [ContinuousAt, ← Subtype.coe_eta (f x) (f x).2, nhds_subtype_eq_comap, Filter.tendsto_comap_iff]
  exact hf

theorem continuousAt_dirPt {x₀ : ↥STW59.sphereFive}
    (h : equatorInv ((x₀ : Fin 3 → ℂ)) ≠ 0) : ContinuousAt dirPt x₀ := by
  refine continuousAt_subtype_mk ?_
  have hc : Continuous fun x : ↥STW59.sphereFive => equatorInv ((x : Fin 3 → ℂ)) :=
    continuous_equatorInv.comp continuous_subtype_val
  have hopen : IsOpen {x : ↥STW59.sphereFive | equatorInv ((x : Fin 3 → ℂ)) ≠ 0} :=
    isOpen_ne.preimage hc
  have heq : (fun x : ↥STW59.sphereFive => ((dirPt x : EuclideanSpace ℝ (Fin 5))))
      =ᶠ[nhds x₀] fun x : ↥STW59.sphereFive =>
        ‖equatorInv ((x : Fin 3 → ℂ))‖⁻¹ • equatorInv ((x : Fin 3 → ℂ)) :=
    Filter.eventually_of_mem (hopen.mem_nhds h) fun x hx => coe_dirPt_of_ne hx
  refine ContinuousAt.congr ?_ heq.symm
  exact ContinuousAt.smul (ContinuousAt.inv₀ hc.norm.continuousAt (norm_ne_zero_iff.mpr h))
    hc.continuousAt

theorem equatorEmb_dirPt {x : ↥STW59.sphereFive} (h : ((x : Fin 3 → ℂ) 2).re = 0) :
    equatorEmb ((dirPt x : EuclideanSpace ℝ (Fin 5))) = (x : Fin 3 → ℂ) := by
  have hx : (x : Fin 3 → ℂ) ∈ STW59.unitVectors (Fin 3) := x.2
  have hn : ‖equatorInv ((x : Fin 3 → ℂ))‖ ^ 2 = 1 := by
    rw [norm_sq_equatorInv hx, h]
    ring
  have hn1 : ‖equatorInv ((x : Fin 3 → ℂ))‖ = 1 := by
    nlinarith [norm_nonneg (equatorInv ((x : Fin 3 → ℂ)))]
  have hne : equatorInv ((x : Fin 3 → ℂ)) ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hn1
    exact zero_ne_one hn1
  rw [coe_dirPt_of_ne hne, hn1, inv_one, one_smul, equatorEmb_equatorInv h]

/-! ### The frames near the two poles -/

theorem isOpen_neSouthPole : IsOpen {x : ↥STW59.sphereFive | (x : Fin 3 → ℂ) 2 ≠ -1} :=
  isOpen_ne.preimage ((continuous_apply 2).comp continuous_subtype_val)

theorem isOpen_neNorthPole : IsOpen {x : ↥STW59.sphereFive | (x : Fin 3 → ℂ) 2 ≠ 1} :=
  isOpen_ne.preimage ((continuous_apply 2).comp continuous_subtype_val)

theorem continuousAt_frameNorth {x₀ : ↥STW59.sphereFive} (h : (x₀ : Fin 3 → ℂ) 2 ≠ -1) :
    ContinuousAt (fun x : ↥STW59.sphereFive => frameNorth e3 ((x : Fin 3 → ℂ))) x₀ := by
  have hOn : ContinuousOn (fun x : ↥STW59.sphereFive => frameNorth e3 ((x : Fin 3 → ℂ)))
      {x : ↥STW59.sphereFive | (x : Fin 3 → ℂ) 2 ≠ -1} := by
    rw [continuousOn_iff_continuous_restrict]
    exact continuous_frameRot continuous_const
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun s => isFrameDatum_e3 s.1.2 s.2)
  exact hOn.continuousAt (isOpen_neSouthPole.mem_nhds h)

theorem continuousAt_frameSouth {x₀ : ↥STW59.sphereFive} (h : (x₀ : Fin 3 → ℂ) 2 ≠ 1) :
    ContinuousAt (fun x : ↥STW59.sphereFive => frameSouth e3 ((x : Fin 3 → ℂ))) x₀ := by
  have hOn : ContinuousOn (fun x : ↥STW59.sphereFive => frameSouth e3 ((x : Fin 3 → ℂ)))
      {x : ↥STW59.sphereFive | (x : Fin 3 → ℂ) 2 ≠ 1} := by
    rw [continuousOn_iff_continuous_restrict]
    exact (continuous_frameRot continuous_const
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun s => isFrameDatum_neg_e3 s.1.2 s.2)).mul continuous_const
  exact hOn.continuousAt (isOpen_neNorthPole.mem_nhds h)

end Cone

/-! ## 7. The two hemisphere fields -/

section Fields

variable {HI : Type*} [Fintype HI] [DecidableEq HI]
variable {Y : Type*} [TopologicalSpace Y]

/-- The northern field: the northern frame, padded by the identity of `H`. -/
def northF (HI : Type*) [Fintype HI] [DecidableEq HI] (x : Fin 3 → ℂ) :
    Matrix (Fin 3 ⊕ HI) (Fin 3 ⊕ HI) ℂ :=
  frame3 HI (frameNorth e3 x)

/-- The southern field at a point of `S⁵` and a point of `Y`. -/
def southAt (P c : Y → Matrix HI HI ℂ)
    (W : ℝ → ↥STW59.sphereFour → Y → Matrix (Fin 2 ⊕ HI) (Fin 2 ⊕ HI) ℂ)
    (x : ↥STW59.sphereFive) (y : Y) : Matrix (Fin 3 ⊕ HI) (Fin 3 ⊕ HI) ℂ :=
  frame3 HI (frameSouth e3 ((x : Fin 3 → ℂ))) * (ext3 P y (W (capTime x) (dirPt x) y))ᴴ
    * ext3 P y (Matrix.fromBlocks 1 0 0 (c y))

/-- The southern field over `S⁵ × Y`. -/
def southF (P c : Y → Matrix HI HI ℂ)
    (W : ℝ → ↥STW59.sphereFour → Y → Matrix (Fin 2 ⊕ HI) (Fin 2 ⊕ HI) ℂ)
    (q : ↥STW59.sphereFive × Y) : Matrix (Fin 3 ⊕ HI) (Fin 3 ⊕ HI) ℂ :=
  southAt P c W q.1 q.2

variable {P c : Y → Matrix HI HI ℂ}
  {W : ℝ → ↥STW59.sphereFour → Y → Matrix (Fin 2 ⊕ HI) (Fin 2 ⊕ HI) ℂ} {y : Y}

theorem northF_star_mul {x : Fin 3 → ℂ} (hx : x ∈ STW59.unitVectors (Fin 3)) (hN : x 2 ≠ -1) :
    (northF HI x)ᴴ * northF HI x = 1 :=
  frame3_star_mul (frameNorth_conjTranspose_mul_self (isFrameDatum_e3 hx hN))

theorem northF_conj {x : Fin 3 → ℂ} (hx : x ∈ STW59.unitVectors (Fin 3)) (hN : x 2 ≠ -1)
    (P : Y → Matrix HI HI ℂ) (y : Y) :
    northF HI x * bigE P y * (northF HI x)ᴴ = bigF P x y :=
  frame3_conj_bigE P y (frameNorth_conj_eq_compl hx hN)

theorem isCornerUnit_cBlock (hc1 : (c y)ᴴ * c y = P y) (hc2 : c y * (c y)ᴴ = P y) :
    IsCornerUnit P y (Matrix.fromBlocks 1 0 0 (c y)) where
  star_mul := by
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_one, fromBlocks_diag_mul_rect, Matrix.one_mul, hc1, cornerE]
  mul_star := by
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_one, fromBlocks_diag_mul_rect, Matrix.one_mul, hc2, cornerE]

theorem isCornerUnit_genBlock {x : Fin 3 → ℂ} (hx : x ∈ STW59.unitVectors (Fin 3))
    (hN : x 2 ≠ -1) (hS : x 2 ≠ 1) (hP : P y * P y = P y) (hPs : (P y)ᴴ = P y) :
    IsCornerUnit P y (Matrix.fromBlocks (genU2 x) 0 0 (P y)) where
  star_mul := by
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      fromBlocks_diag_mul_rect, genU2_conjTranspose_mul_self hx hN hS, hPs, hP, cornerE]
  mul_star := by
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      fromBlocks_diag_mul_rect, genU2_mul_conjTranspose hx hN hS, hPs, hP, cornerE]

theorem ext3_genBlock {x : Fin 3 → ℂ} (hx : x ∈ STW59.unitVectors (Fin 3))
    (hN : x 2 ≠ -1) (hS : x 2 ≠ 1) (P : Y → Matrix HI HI ℂ) (y : Y) :
    ext3 P y (Matrix.fromBlocks (genU2 x) 0 0 (P y)) = frame3 HI (genU x) := by
  have h1 : P y + (1 - P y) = (1 : Matrix HI HI ℂ) := by abel
  rw [ext3_fromBlocks, incl_genU2_add hx hN hS, h1, frame3]

theorem ext3_cBlock (P c : Y → Matrix HI HI ℂ) (y : Y) :
    ext3 P y (Matrix.fromBlocks 1 0 0 (c y)) = coframe3 HI (c y + (1 - P y)) := by
  have h1 : incl * (1 : Matrix (Fin 2) (Fin 2) ℂ) * inclᴴ + rk1 e3 e3
      = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    rw [Matrix.mul_one, incl_mul_conjTranspose]
    abel
  rw [ext3_fromBlocks, h1, coframe3]

/-- **The seam.**  On the equator the two hemisphere fields agree. -/
theorem southAt_eq_northF (hP : ∀ y, P y * P y = P y) (hPs : ∀ y, (P y)ᴴ = P y)
    (hc1 : ∀ y, (c y)ᴴ * c y = P y) (hc2 : ∀ y, c y * (c y)ᴴ = P y)
    (hW1 : ∀ v y, W 1 v y
      = Matrix.fromBlocks (genU2 (equatorEmb (v : EuclideanSpace ℝ (Fin 5)))) 0 0 (c y))
    (x : ↥STW59.sphereFive) (y : Y) (hq : ((x : Fin 3 → ℂ) 2).re = 0) :
    southAt P c W x y = northF HI ((x : Fin 3 → ℂ)) := by
  have hx : (x : Fin 3 → ℂ) ∈ STW59.unitVectors (Fin 3) := x.2
  have hN : (x : Fin 3 → ℂ) 2 ≠ -1 := ne_neg_one_of_re_eq_zero hq
  have hS : (x : Fin 3 → ℂ) 2 ≠ 1 := ne_one_of_re_eq_zero hq
  have hPc : P y * c y = c y := proj_mul_of_partial (hc1 y) (hc2 y) (hP y)
  have hsplit : W (capTime x) (dirPt x) y
      = Matrix.fromBlocks (genU2 ((x : Fin 3 → ℂ))) 0 0 (P y)
        * Matrix.fromBlocks 1 0 0 (c y) := by
    rw [capTime_eq_one hq, hW1, equatorEmb_dirPt hq, fromBlocks_diag_mul_rect, Matrix.mul_one,
      hPc]
  have hg := isCornerUnit_genBlock (P := P) (y := y) hx hN hS (hP y) (hPs y)
  have hcb := isCornerUnit_cBlock (P := P) (y := y) (hc1 y) (hc2 y)
  have hCu : (coframe3 HI (c y + (1 - P y)))ᴴ * coframe3 HI (c y + (1 - P y)) = 1 := by
    have := ext3_conjTranspose_mul_self hcb (hP y) (hPs y)
    rwa [ext3_cBlock] at this
  have hext : ext3 P y (W (capTime x) (dirPt x) y)
      = frame3 HI (genU ((x : Fin 3 → ℂ))) * coframe3 HI (c y + (1 - P y)) := by
    rw [hsplit, ext3_mul hg hcb (hP y), ext3_genBlock hx hN hS, ext3_cBlock]
  have hcomm : (coframe3 HI (c y + (1 - P y)))ᴴ * frame3 HI (genU ((x : Fin 3 → ℂ)))ᴴ
      = frame3 HI (genU ((x : Fin 3 → ℂ)))ᴴ * (coframe3 HI (c y + (1 - P y)))ᴴ := by
    rw [coframe3_conjTranspose, frame3_comm_coframe3]
  rw [southAt, hext, ext3_cBlock, Matrix.conjTranspose_mul, frame3_conjTranspose]
  calc frame3 HI (frameSouth e3 ((x : Fin 3 → ℂ)))
        * ((coframe3 HI (c y + (1 - P y)))ᴴ * frame3 HI (genU ((x : Fin 3 → ℂ)))ᴴ)
        * coframe3 HI (c y + (1 - P y))
      = frame3 HI (frameSouth e3 ((x : Fin 3 → ℂ))) * frame3 HI (genU ((x : Fin 3 → ℂ)))ᴴ
          * ((coframe3 HI (c y + (1 - P y)))ᴴ * coframe3 HI (c y + (1 - P y))) := by
        rw [hcomm]
        simp only [Matrix.mul_assoc]
    _ = northF HI ((x : Fin 3 → ℂ)) := by
        rw [hCu, Matrix.mul_one, frame3_mul, frameSouth_mul_genU_conjTranspose hx hS, northF]

theorem southAt_star_mul (hP : ∀ y, P y * P y = P y) (hPs : ∀ y, (P y)ᴴ = P y)
    (hc1 : ∀ y, (c y)ᴴ * c y = P y) (hc2 : ∀ y, c y * (c y)ᴴ = P y)
    (hWu : ∀ t v y, IsCornerUnit P y (W t v y))
    (x : ↥STW59.sphereFive) (y : Y) (hq : ((x : Fin 3 → ℂ) 2).re ≤ 0) :
    (southAt P c W x y)ᴴ * southAt P c W x y = 1 := by
  have hS : (x : Fin 3 → ℂ) 2 ≠ 1 := by
    intro hc
    rw [hc] at hq
    norm_num at hq
  have h1 : (frame3 HI (frameSouth e3 ((x : Fin 3 → ℂ))))ᴴ
      * frame3 HI (frameSouth e3 ((x : Fin 3 → ℂ))) = 1 :=
    frame3_star_mul (frameSouth_conjTranspose_mul_self unit_e3 (isFrameDatum_neg_e3 x.2 hS))
  have h2 : ((ext3 P y (W (capTime x) (dirPt x) y))ᴴ)ᴴ
      * (ext3 P y (W (capTime x) (dirPt x) y))ᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact ext3_mul_conjTranspose (hWu _ _ _) (hP y) (hPs y)
  have h3 : (ext3 P y (Matrix.fromBlocks 1 0 0 (c y)))ᴴ
      * ext3 P y (Matrix.fromBlocks 1 0 0 (c y)) = 1 :=
    ext3_conjTranspose_mul_self (isCornerUnit_cBlock (hc1 y) (hc2 y)) (hP y) (hPs y)
  exact mul_star_mul_of_unitary (mul_star_mul_of_unitary h1 h2) h3

theorem southAt_conj (hP : ∀ y, P y * P y = P y) (hPs : ∀ y, (P y)ᴴ = P y)
    (hc1 : ∀ y, (c y)ᴴ * c y = P y) (hc2 : ∀ y, c y * (c y)ᴴ = P y)
    (hWu : ∀ t v y, IsCornerUnit P y (W t v y))
    (x : ↥STW59.sphereFive) (y : Y) (hq : ((x : Fin 3 → ℂ) 2).re ≤ 0) :
    southAt P c W x y * bigE P y * (southAt P c W x y)ᴴ = bigF P ((x : Fin 3 → ℂ)) y := by
  have hS : (x : Fin 3 → ℂ) 2 ≠ 1 := by
    intro hc
    rw [hc] at hq
    norm_num at hq
  have h2 : (ext3 P y (W (capTime x) (dirPt x) y))ᴴ
      * ((ext3 P y (W (capTime x) (dirPt x) y))ᴴ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact ext3_conjTranspose_mul_self (hWu _ _ _) (hP y) (hPs y)
  have h3 : ext3 P y (Matrix.fromBlocks 1 0 0 (c y))
      * (ext3 P y (Matrix.fromBlocks 1 0 0 (c y)))ᴴ = 1 :=
    ext3_mul_conjTranspose (isCornerUnit_cBlock (hc1 y) (hc2 y)) (hP y) (hPs y)
  have h4 : (ext3 P y (W (capTime x) (dirPt x) y))ᴴ * bigE P y
      = bigE P y * (ext3 P y (W (capTime x) (dirPt x) y))ᴴ :=
    conjTranspose_comm_of_comm (conjTranspose_bigE (hPs y))
      (ext3_comm_bigE (hWu _ _ _) (hP y))
  have h5 : ext3 P y (Matrix.fromBlocks 1 0 0 (c y)) * bigE P y
      = bigE P y * ext3 P y (Matrix.fromBlocks 1 0 0 (c y)) :=
    ext3_comm_bigE (isCornerUnit_cBlock (hc1 y) (hc2 y)) (hP y)
  have h6 : frame3 HI (frameSouth e3 ((x : Fin 3 → ℂ))) * bigE P y
      * (frame3 HI (frameSouth e3 ((x : Fin 3 → ℂ))))ᴴ = bigF P ((x : Fin 3 → ℂ)) y :=
    frame3_conj_bigE P y (frameSouth_conj_eq_compl x.2 hS)
  simp only [southAt]
  exact conj_triple h2 h3 h4 h5 h6

theorem continuousAt_southF (hPc : Continuous P) (hcc : Continuous c)
    (hWc : Continuous fun r : ℝ × ↥STW59.sphereFour × Y => W r.1 r.2.1 r.2.2)
    (hW0 : ∀ v y, W 0 v y = cornerE P y)
    {q₀ : ↥STW59.sphereFive × Y} (hq : ((q₀.1 : Fin 3 → ℂ) 2).re ≤ 0) :
    ContinuousAt (southF P c W) q₀ := by
  have hS : (q₀.1 : Fin 3 → ℂ) 2 ≠ 1 := by
    intro hc'
    rw [hc'] at hq
    norm_num at hq
  have h1 : ContinuousAt (fun q : ↥STW59.sphereFive × Y =>
      frame3 HI (frameSouth e3 ((q.1 : Fin 3 → ℂ)))) q₀ :=
    (continuous_frame3.continuousAt).comp ((continuousAt_frameSouth hS).comp continuousAt_fst)
  have hcorr : ContinuousAt (fun q : ↥STW59.sphereFive × Y =>
      W (capTime q.1) (dirPt q.1) q.2) q₀ := by
    rcases lt_or_ge ((q₀.1 : Fin 3 → ℂ) 2).re (-(1 / 2)) with hlt | hge
    · have hopen : IsOpen {q : ↥STW59.sphereFive × Y | ((q.1 : Fin 3 → ℂ) 2).re < -(1 / 2)} :=
        isOpen_lt (continuous_capHeight.comp continuous_fst) continuous_const
      have heq : (fun q : ↥STW59.sphereFive × Y => W (capTime q.1) (dirPt q.1) q.2)
          =ᶠ[nhds q₀] fun q : ↥STW59.sphereFive × Y => cornerE P q.2 :=
        Filter.eventually_of_mem (hopen.mem_nhds hlt) fun q hq' => by
          show W (capTime q.1) (dirPt q.1) q.2 = cornerE P q.2
          rw [capTime_eq_zero (le_of_lt hq'), hW0]
      exact ContinuousAt.congr
        ((continuous_cornerE hPc).continuousAt.comp continuousAt_snd) heq.symm
    · have hlt1 : ((q₀.1 : Fin 3 → ℂ) 2).re ^ 2 < 1 := by nlinarith
      have hne : equatorInv ((q₀.1 : Fin 3 → ℂ)) ≠ 0 := equatorInv_ne_zero q₀.1.2 hlt1
      exact hWc.continuousAt.comp
        ((continuous_capTime.continuousAt.comp continuousAt_fst).prodMk
          (((continuousAt_dirPt hne).comp continuousAt_fst).prodMk continuousAt_snd))
  have h2 : ContinuousAt (fun q : ↥STW59.sphereFive × Y =>
      (ext3 P q.2 (W (capTime q.1) (dirPt q.1) q.2))ᴴ) q₀ :=
    (continuous_id.matrix_conjTranspose.continuousAt).comp
      (continuousAt_ext3 hPc hcorr continuousAt_snd)
  have h3 : ContinuousAt (fun q : ↥STW59.sphereFive × Y =>
      ext3 P q.2 (Matrix.fromBlocks 1 0 0 (c q.2))) q₀ :=
    continuousAt_ext3 hPc ((Continuous.matrix_fromBlocks continuous_const continuous_const
      continuous_const hcc).continuousAt.comp continuousAt_snd) continuousAt_snd
  exact (h1.mul h2).mul h3

/-- **The analytic half of Corollary 4.**  A null-homotopy of `u ⊕ c` inside the
corner produces a continuous unitary field of the ambient carrying the constant
complement to the moving one. -/
theorem exists_unitary_field_of_nullHomotopy
    (hPc : Continuous P) (hP : ∀ y, P y * P y = P y) (hPs : ∀ y, (P y)ᴴ = P y)
    (hcc : Continuous c) (hc1 : ∀ y, (c y)ᴴ * c y = P y) (hc2 : ∀ y, c y * (c y)ᴴ = P y)
    (hWc : Continuous fun r : ℝ × ↥STW59.sphereFour × Y => W r.1 r.2.1 r.2.2)
    (hWu : ∀ t v y, IsCornerUnit P y (W t v y))
    (hW0 : ∀ v y, W 0 v y = cornerE P y)
    (hW1 : ∀ v y, W 1 v y
      = Matrix.fromBlocks (genU2 (equatorEmb (v : EuclideanSpace ℝ (Fin 5)))) 0 0 (c y)) :
    ∃ G : ↥STW59.sphereFive × Y → Matrix (Fin 3 ⊕ HI) (Fin 3 ⊕ HI) ℂ, Continuous G ∧
      (∀ q, (G q)ᴴ * G q = 1) ∧
      (∀ q, G q * bigE P q.2 * (G q)ᴴ = bigF P ((q.1 : Fin 3 → ℂ)) q.2) := by
  refine ⟨fun q => if 0 ≤ ((q.1 : Fin 3 → ℂ) 2).re then northF HI ((q.1 : Fin 3 → ℂ))
    else southF P c W q, ?_, ?_, ?_⟩
  · refine continuous_if_le continuous_const (continuous_capHeight.comp continuous_fst)
      (fun q hq => ?_) (fun q hq => ?_) (fun q hq => ?_)
    · exact (continuous_frame3.continuousAt.comp
        ((continuousAt_frameNorth (ne_neg_one_of_mem_northCap hq)).comp
          continuousAt_fst)).continuousWithinAt
    · exact (continuousAt_southF hPc hcc hWc hW0 hq).continuousWithinAt
    · exact (southAt_eq_northF hP hPs hc1 hc2 hW1 q.1 q.2 hq.symm).symm
  · intro q
    dsimp only
    split_ifs with h
    · exact northF_star_mul q.1.2 (ne_neg_one_of_mem_northCap h)
    · exact southAt_star_mul hP hPs hc1 hc2 hWu q.1 q.2 (le_of_lt (not_le.mp h))
  · intro q
    dsimp only
    split_ifs with h
    · exact northF_conj q.1.2 (ne_neg_one_of_mem_northCap h) P q.2
    · exact southAt_conj hP hPs hc1 hc2 hWu q.1 q.2 (le_of_lt (not_le.mp h))

end Fields

end

end LIX
end GroupApproximation
