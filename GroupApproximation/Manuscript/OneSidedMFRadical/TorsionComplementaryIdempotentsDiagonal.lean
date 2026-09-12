import GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotentsWeyl
import GroupApproximation.Leavitt.OneSidedCompressor

/-!
# The printed diagonal `D(a) = diag(1,1,1,a)` and its elementary factorisation

`non_mf_groups_exist.tex`, Proposition `prop:torsion-defect-ring`, the proof:

> Write `D(a) = diag(1,1,1,a)`; for `i ≠ j`,
> `D(1 ± f_{ij}) = [e_{41}(f_{ii}), e_{14}(± f_{ij})]` lies in `EL₄(S)`.

Coordinates are 0-indexed here, as everywhere in
`GroupApproximation.OneSidedCompressor`: the printed coordinates `1,2,3` are
`coreIdx 0, coreIdx 1, coreIdx 2` and the printed fourth coordinate is
`lastIdx = 3`.  So the printed `e_{41}` is
`elementaryRoot lastIdx (coreIdx 0)` and the printed `e_{14}` is
`elementaryRoot (coreIdx 0) lastIdx`.

The commutator identity is a `2 × 2` block calculation that needs nothing but
`y x = 0` and two square-zero relations, and it is isolated here as
`one_add_commutator_of_square_zero`, a statement about an arbitrary ring: for
`X² = Y² = YX = 0`,

  `(1+X)(1+Y)(1-X)(1-Y) = 1 + XY`.

Applied to `X = e·E_{41}` and `Y = ±f_{ij}·E_{14}` — whose product is
`±f_{ij}·E_{44}`, and whose reversed product carries the coefficient
`f_{ij}f_{ii} = 0` — it gives exactly the printed `D(1 ± f_{ij})`.

The module also records that `D(a)` centralises the printed core
`L = EL₃(S)`: a diagonal matrix supported on the fourth coordinate commutes
with every elementary matrix on the first three.  That is the printed
"`D(r)` centralizes `L`" and the printed `c ∈ C_B(L)`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TorsionComplementaryIdempotents

open GroupApproximation.OneSidedCompressor
open scoped commutatorElement

universe u

variable {R : Type u} [Ring R]

/-! ## Coercion helpers for the elementary group -/

section Coe

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix of an elementary unit. -/
theorem elementaryUnit_matrix (i j : ι) (h : i ≠ j) (a : R) :
    ((elementaryUnit i j h a : (Matrix ι ι R)ˣ) : Matrix ι ι R)
      = 1 + Matrix.single i j a := rfl

/-- The matrix of an elementary root. -/
theorem elementaryRoot_matrix (i j : ι) (h : i ≠ j) (a : R) :
    ((elementaryRoot i j h a : (Matrix ι ι R)ˣ) : Matrix ι ι R)
      = 1 + Matrix.single i j a := rfl

theorem elementaryGroup_val_mul (x y : elementaryGroup ι R) :
    (((x * y : elementaryGroup ι R) : (Matrix ι ι R)ˣ) : Matrix ι ι R)
      = ((x : (Matrix ι ι R)ˣ) : Matrix ι ι R) *
        ((y : (Matrix ι ι R)ˣ) : Matrix ι ι R) := rfl

theorem elementaryGroup_val_inv (x : elementaryGroup ι R) :
    (((x⁻¹ : elementaryGroup ι R) : (Matrix ι ι R)ˣ) : Matrix ι ι R)
      = (((x : (Matrix ι ι R)ˣ)⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) := rfl

/-- Two elements of the elementary group are equal as soon as their matrices
are. -/
theorem elementaryGroup_ext {x y : elementaryGroup ι R}
    (h : ((x : (Matrix ι ι R)ˣ) : Matrix ι ι R)
      = ((y : (Matrix ι ι R)ˣ) : Matrix ι ι R)) : x = y :=
  Subtype.ext (Units.ext h)

end Coe

/-! ## The square-zero commutator, in an arbitrary ring -/

/-- The `2 × 2` block identity behind the printed
`D(1 ± f_{ij}) = [e_{41}(f_{ii}), e_{14}(± f_{ij})]`.

If `X² = Y² = 0` and `YX = 0`, then every word of length `≥ 2` occurring in the
expansion vanishes except `XY` itself, and the group commutator collapses to
`1 + XY`. -/
theorem one_add_commutator_of_square_zero {A : Type*} [Ring A] {X Y : A}
    (hXX : X * X = 0) (hYY : Y * Y = 0) (hYX : Y * X = 0) :
    (1 + X) * (1 + Y) * (1 - X) * (1 - Y) = 1 + X * Y := by
  have hXZ : X * (X * Y) = 0 := by rw [← mul_assoc, hXX, zero_mul]
  have hZX : X * Y * X = 0 := by rw [mul_assoc, hYX, mul_zero]
  have hZY : X * Y * Y = 0 := by rw [mul_assoc, hYY, mul_zero]
  have hYZ : Y * (X * Y) = 0 := by rw [← mul_assoc, hYX, zero_mul]
  have hZZ : X * Y * (X * Y) = 0 := by rw [← mul_assoc, hZX, zero_mul]
  have hsplit : (1 + X) * (1 + Y) * (1 - X) * (1 - Y)
      = ((1 + X) * (1 + Y)) * ((1 - X) * (1 - Y)) := by noncomm_ring
  have e1 : (1 + X) * (1 + Y) = 1 + X + Y + X * Y := by noncomm_ring
  have e2 : (1 - X) * (1 - Y) = 1 - X - Y + X * Y := by noncomm_ring
  rw [hsplit, e1, e2]
  calc (1 + X + Y + X * Y) * (1 - X - Y + X * Y)
      = (1 - X - Y + X * Y)
        + (X - X * X - X * Y + X * (X * Y))
        + (Y - Y * X - Y * Y + Y * (X * Y))
        + (X * Y - X * Y * X - X * Y * Y + X * Y * (X * Y)) := by noncomm_ring
    _ = 1 + X * Y := by rw [hXX, hXZ, hYX, hYY, hYZ, hZX, hZY, hZZ]; abel

/-! ## The printed diagonal -/

/-- **Printed:** `D(a) = diag(1,1,1,a)`. -/
def lastDiag (a : R) : Matrix (Fin 4) (Fin 4) R :=
  Matrix.diagonal (fun k ↦ if k = lastIdx then a else 1)

@[simp] theorem lastDiag_one : lastDiag (1 : R) = 1 := by
  rw [lastDiag]
  simp

/-- `D` is multiplicative: `D(a)D(b) = D(ab)`. -/
theorem lastDiag_mul (a b : R) : lastDiag a * lastDiag b = lastDiag (a * b) := by
  rw [lastDiag, lastDiag, lastDiag, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases h : k = lastIdx <;> simp [h]

/-- `D(1 + z) = 1 + z E_{44}`: the form in which the commutator identity
delivers it. -/
theorem lastDiag_one_add (z : R) :
    lastDiag (1 + z) = 1 + Matrix.single lastIdx lastIdx z := by
  ext r c
  fin_cases r <;> fin_cases c <;> simp [lastDiag, lastIdx]

/-- `D(a)` commutes with every elementary matrix on the first three
coordinates. -/
theorem lastDiag_commute_single (a b : R) {p q : Fin 4} (hp : p ≠ lastIdx)
    (hq : q ≠ lastIdx) :
    lastDiag a * Matrix.single p q b = Matrix.single p q b * lastDiag a := by
  ext r c
  rw [lastDiag, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  by_cases h : p = r ∧ q = c
  · obtain ⟨hr, hc⟩ := h
    subst hr
    subst hc
    simp [hp, hq]
  · simp [h]

/-! ## The printed commutator `D(1 + xy) = [e₄₁(x), e₁₄(y)]` -/

/-- The printed pair of elementary roots, as a group element. -/
def diagRoot (x y : R) : elementaryGroup (Fin 4) R :=
  ⁅elementaryRoot lastIdx (coreIdx 0) (last_ne_coreIdx 0) x,
    elementaryRoot (coreIdx 0) lastIdx (coreIdx_ne_last 0) y⁆

/-- **The printed identity `D(1 + xy) = [e₄₁(x), e₁₄(y)]`**, whenever
`yx = 0`. -/
theorem diagRoot_matrix {x y : R} (hyx : y * x = 0) :
    ((diagRoot x y : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R)
      = lastDiag (1 + x * y) := by
  have hXX : Matrix.single lastIdx (coreIdx 0) x *
      Matrix.single lastIdx (coreIdx 0) x = 0 :=
    Matrix.single_mul_single_of_ne (c := x) lastIdx (coreIdx 0) lastIdx
      (coreIdx_ne_last 0) x
  have hYY : Matrix.single (coreIdx 0) lastIdx y *
      Matrix.single (coreIdx 0) lastIdx y = 0 :=
    Matrix.single_mul_single_of_ne (c := y) (coreIdx 0) lastIdx (coreIdx 0)
      (last_ne_coreIdx 0) y
  have hYX : Matrix.single (coreIdx 0) lastIdx y *
      Matrix.single lastIdx (coreIdx 0) x = 0 := by
    rw [Matrix.single_mul_single_same, hyx, Matrix.single_zero]
  have hXY : Matrix.single lastIdx (coreIdx 0) x *
      Matrix.single (coreIdx 0) lastIdx y
      = Matrix.single lastIdx lastIdx (x * y) :=
    Matrix.single_mul_single_same (c := x) lastIdx (coreIdx 0) lastIdx y
  rw [lastDiag_one_add, ← hXY]
  change (1 + Matrix.single lastIdx (coreIdx 0) x) *
      (1 + Matrix.single (coreIdx 0) lastIdx y) *
      (1 - Matrix.single lastIdx (coreIdx 0) x) *
      (1 - Matrix.single (coreIdx 0) lastIdx y) = _
  exact one_add_commutator_of_square_zero hXX hYY hYX

/-! ## The printed instances `D(1 ± f_{ij})` -/

section Instances

variable (P : OneSidedInverse R)

/-- **Printed:** `D(1 + f_{ij}) = [e₄₁(f_{ii}), e₁₄(f_{ij})]`. -/
def diagPlus (i j : ℕ) : elementaryGroup (Fin 4) R :=
  diagRoot (fUnit P i i) (fUnit P i j)

/-- **Printed:** `D(1 - f_{ij}) = [e₄₁(f_{ii}), e₁₄(-f_{ij})]`. -/
def diagMinus (i j : ℕ) : elementaryGroup (Fin 4) R :=
  diagRoot (fUnit P i i) (-fUnit P i j)

theorem diagPlus_matrix {i j : ℕ} (hij : i ≠ j) :
    ((diagPlus P i j : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R)
      = lastDiag (1 + fUnit P i j) := by
  have hyx : fUnit P i j * fUnit P i i = 0 := fUnit_mul_of_ne P i i (Ne.symm hij)
  rw [diagPlus, diagRoot_matrix hyx, fUnit_mul_of_eq P i i j]

theorem diagMinus_matrix {i j : ℕ} (hij : i ≠ j) :
    ((diagMinus P i j : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R)
      = lastDiag (1 - fUnit P i j) := by
  have hyx : (-fUnit P i j) * fUnit P i i = 0 := by
    rw [neg_mul, fUnit_mul_of_ne P i i (Ne.symm hij), neg_zero]
  rw [diagMinus, diagRoot_matrix hyx, mul_neg, fUnit_mul_of_eq P i i j,
    ← sub_eq_add_neg]

/-! ### `D(r)` -/

/-- **Printed:** `D(r)` for `r = w_{14}w_{25}`, as the product of the six
elementary commutators the printed factorisation of `r` supplies. -/
def diagR : elementaryGroup (Fin 4) R :=
  diagPlus P 4 1 * diagMinus P 1 4 * diagPlus P 4 1 *
    (diagPlus P 5 2 * diagMinus P 2 5 * diagPlus P 5 2)

theorem four_ne_one : (4 : ℕ) ≠ 1 := by decide

theorem five_ne_two : (5 : ℕ) ≠ 2 := by decide

/-- **`D(r)` is the printed diagonal of the printed conjugator.** -/
theorem diagR_matrix :
    ((diagR P : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R)
      = lastDiag ((rUnit P : Rˣ) : R) := by
  rw [diagR]
  simp only [elementaryGroup_val_mul, diagPlus_matrix P four_ne_one,
    diagMinus_matrix P one_ne_four, diagPlus_matrix P five_ne_two,
    diagMinus_matrix P two_ne_five, lastDiag_mul]
  rw [rUnit_val, weylUnit_val_word P one_ne_four, weylUnit_val_word P two_ne_five]

end Instances

/-! ## `D(a)` centralises the printed core -/

/-- Every group element whose matrix is a `D(a)` commutes with the printed core
`L = EL₃(R)` on coordinates `1,2,3`. -/
theorem core_le_centralizer_of_lastDiag (X : elementaryGroup (Fin 4) R) (a : R)
    (hX : ((X : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R)
      = lastDiag a) :
    core R ≤ Subgroup.centralizer ({X} : Set (elementaryGroup (Fin 4) R)) := by
  rw [core, Subgroup.closure_le]
  rintro g ⟨i, j, hij, b, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  rintro h hmem
  rw [Set.mem_singleton_iff] at hmem
  subst hmem
  refine elementaryGroup_ext ?_
  rw [elementaryGroup_val_mul, elementaryGroup_val_mul, hX, elementaryRoot_matrix,
    mul_add, add_mul, mul_one, one_mul,
    lastDiag_commute_single a b (coreIdx_ne_last i) (coreIdx_ne_last j)]

/-- **Printed:** `D(a)` centralises `L`, in the form the printed defect asks
for it. -/
theorem lastDiag_commute_core (X : elementaryGroup (Fin 4) R) (a : R)
    (hX : ((X : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R)
      = lastDiag a) :
    ∀ g ∈ core R, Commute X g := by
  intro g hg
  have hc := core_le_centralizer_of_lastDiag X a hX hg
  rw [Subgroup.mem_centralizer_iff] at hc
  show X * g = g * X
  exact hc X (Set.mem_singleton X)

end TorsionComplementaryIdempotents
end OneSidedMFRadical
end Manuscript
end GroupApproximation
