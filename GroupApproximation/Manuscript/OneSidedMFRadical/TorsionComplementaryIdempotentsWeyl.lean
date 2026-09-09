import GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotentsMatrixUnits

/-!
# The printed Weyl words `w_{ij}` and the conjugator `r = w_{14}w_{25}`

`non_mf_groups_exist.tex`, Proposition `prop:torsion-defect-ring`, the proof:

> Let `u` be the compressor of Lemma `lem:ring-compression-cell`, put
> `w_{ij} = (1+f_{ji})(1-f_{ij})(1+f_{ji})`, `r = w_{14}w_{25}`, and `v = uD(r)`.

and the four identities the printed proof then uses:

> from `r f_{02} r^{-1} = f_{05}`, `r f_{12} r^{-1} = f_{45}`,
> `f_{02}t^3 = f_{05}`, and `t^3 f_{45} = f_{12}t^3`, direct multiplication with
> the displayed `u` gives `v c v^{-1} = e_{14}(f_{02})` and `v z v^{-1} = z`.

This module is the ring half of that sentence: `r` is built here as an honest
unit of `R`, its normal form and the normal form of its inverse are computed,
and the four displayed identities are proved.  The `4 × 4` matrix half is
`TorsionComplementaryIdempotentsDiagonal` and
`TorsionComplementaryIdempotentsCell`.

`w_{ij}` is a unit for a reason that costs nothing: each of its three printed
factors is `1 + x` with `x^2 = 0`, hence a unit with inverse `1 - x`.  So the
printed word is literally a product of three units and its inverse is the
reversed product, whose normal form `1 - f_{ii} - f_{jj} + f_{ij} - f_{ji}` is
computed by the same expansion.

The two conjugations are read off two one-sided rules, which is all the
printed proof needs:

* `w_{ij} f_{ab} = f_{ab}` when `a ∉ {i,j}`, and `w_{ij} f_{ib} = f_{jb}`;
* `f_{ab} w_{ij}^{-1} = f_{ab}` when `b ∉ {i,j}`, and `f_{ai} w_{ij}^{-1} = f_{aj}`.

`r f_{02} r^{-1} = f_{05}` is then `0 ∉ {1,4}`, `0 ∉ {2,5}` on the left and
`2 ↦ 5`, `5 ∉ {1,4}` on the right; `r f_{12} r^{-1} = f_{45}` is `1 ↦ 4` on the
left and `2 ↦ 5` on the right.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TorsionComplementaryIdempotents

open GroupApproximation.OneSidedCompressor

universe u

variable {R : Type u} [Ring R]

/-! ## Square-zero units -/

/-- `1 + x` is a unit whenever `x^2 = 0`, with inverse `1 - x`. -/
def sqzUnit {x : R} (hx : x * x = 0) : Rˣ where
  val := 1 + x
  inv := 1 - x
  val_inv := by noncomm_ring [hx]
  inv_val := by noncomm_ring [hx]

@[simp] theorem sqzUnit_val {x : R} (hx : x * x = 0) :
    ((sqzUnit hx : Rˣ) : R) = 1 + x := rfl

@[simp] theorem sqzUnit_inv_val {x : R} (hx : x * x = 0) :
    (((sqzUnit hx)⁻¹ : Rˣ) : R) = 1 - x := rfl

/-! ## The printed Weyl word -/

section Weyl

variable (P : OneSidedInverse R) {i j : ℕ}

theorem fUnit_swap_sq (hij : i ≠ j) : fUnit P j i * fUnit P j i = 0 :=
  fUnit_mul_self P (Ne.symm hij)

theorem fUnit_neg_sq (hij : i ≠ j) :
    (-fUnit P i j) * (-fUnit P i j) = 0 := by
  rw [neg_mul_neg, fUnit_mul_self P hij]

/-- **Printed:** `w_{ij} = (1+f_{ji})(1-f_{ij})(1+f_{ji})`, as a unit of `R`:
each factor is `1 + x` with `x^2 = 0`. -/
def weylUnit (hij : i ≠ j) : Rˣ :=
  sqzUnit (fUnit_swap_sq P hij) * sqzUnit (fUnit_neg_sq P hij) *
    sqzUnit (fUnit_swap_sq P hij)

/-- The printed word, before any normalisation. -/
theorem weylUnit_val_word (hij : i ≠ j) :
    ((weylUnit P hij : Rˣ) : R) =
      (1 + fUnit P j i) * (1 - fUnit P i j) * (1 + fUnit P j i) := by
  show (1 + fUnit P j i) * (1 + -fUnit P i j) * (1 + fUnit P j i) = _
  rw [← sub_eq_add_neg]

/-- **The normal form of the printed Weyl word:**
`w_{ij} = 1 - f_{ii} - f_{jj} - f_{ij} + f_{ji}`. -/
theorem weylUnit_val (hij : i ≠ j) :
    ((weylUnit P hij : Rˣ) : R) =
      1 - fUnit P i i - fUnit P j j - fUnit P i j + fUnit P j i := by
  have h1 : fUnit P j i * fUnit P i j = fUnit P j j := fUnit_mul_of_eq P j i j
  have h2 : fUnit P i j * fUnit P j i = fUnit P i i := fUnit_mul_of_eq P i j i
  have h3 : fUnit P j i * fUnit P j i = 0 := fUnit_swap_sq P hij
  have h4 : fUnit P j j * fUnit P j i = fUnit P j i := fUnit_mul_of_eq P j j i
  rw [weylUnit_val_word]
  have step1 : (1 + fUnit P j i) * (1 - fUnit P i j)
      = 1 - fUnit P i j + fUnit P j i - fUnit P j j := by
    rw [← h1]; noncomm_ring
  rw [step1]
  have expand : (1 - fUnit P i j + fUnit P j i - fUnit P j j) * (1 + fUnit P j i)
      = 1 + fUnit P j i - fUnit P i j - fUnit P i j * fUnit P j i
          + fUnit P j i + fUnit P j i * fUnit P j i
          - fUnit P j j - fUnit P j j * fUnit P j i := by noncomm_ring
  rw [expand, h2, h3, h4]
  abel

/-- **The normal form of the inverse Weyl word:**
`w_{ij}^{-1} = 1 - f_{ii} - f_{jj} + f_{ij} - f_{ji}`. -/
theorem weylUnit_inv_val (hij : i ≠ j) :
    (((weylUnit P hij)⁻¹ : Rˣ) : R) =
      1 - fUnit P i i - fUnit P j j + fUnit P i j - fUnit P j i := by
  have h1 : fUnit P j i * fUnit P i j = fUnit P j j := fUnit_mul_of_eq P j i j
  have h2 : fUnit P i j * fUnit P j i = fUnit P i i := fUnit_mul_of_eq P i j i
  have h3 : fUnit P j i * fUnit P j i = 0 := fUnit_swap_sq P hij
  have h4 : fUnit P j j * fUnit P j i = fUnit P j i := fUnit_mul_of_eq P j j i
  have hinv : ((weylUnit P hij)⁻¹ : Rˣ) =
      (sqzUnit (fUnit_swap_sq P hij))⁻¹ *
        ((sqzUnit (fUnit_neg_sq P hij))⁻¹ * (sqzUnit (fUnit_swap_sq P hij))⁻¹) := by
    rw [weylUnit, mul_inv_rev, mul_inv_rev]
  have hword : (((weylUnit P hij)⁻¹ : Rˣ) : R) =
      (1 - fUnit P j i) * ((1 + fUnit P i j) * (1 - fUnit P j i)) := by
    rw [hinv]
    simp only [Units.val_mul, sqzUnit_inv_val, sub_neg_eq_add]
  rw [hword, ← mul_assoc]
  have step1 : (1 - fUnit P j i) * (1 + fUnit P i j)
      = 1 + fUnit P i j - fUnit P j i - fUnit P j j := by
    rw [← h1]; noncomm_ring
  rw [step1]
  have expand : (1 + fUnit P i j - fUnit P j i - fUnit P j j) * (1 - fUnit P j i)
      = 1 - fUnit P j i + fUnit P i j - fUnit P i j * fUnit P j i
          - fUnit P j i + fUnit P j i * fUnit P j i
          - fUnit P j j + fUnit P j j * fUnit P j i := by noncomm_ring
  rw [expand, h2, h3, h4]
  abel

/-! ### The two one-sided rules -/

/-- `w_{ij}` fixes `f_{ab}` on the left when `a ∉ {i,j}`. -/
theorem weyl_mul_fUnit_of_ne (hij : i ≠ j) {a : ℕ} (b : ℕ)
    (hai : a ≠ i) (haj : a ≠ j) :
    ((weylUnit P hij : Rˣ) : R) * fUnit P a b = fUnit P a b := by
  have e1 : fUnit P i i * fUnit P a b = 0 := fUnit_mul_of_ne P i b (Ne.symm hai)
  have e2 : fUnit P j j * fUnit P a b = 0 := fUnit_mul_of_ne P j b (Ne.symm haj)
  have e3 : fUnit P i j * fUnit P a b = 0 := fUnit_mul_of_ne P i b (Ne.symm haj)
  have e4 : fUnit P j i * fUnit P a b = 0 := fUnit_mul_of_ne P j b (Ne.symm hai)
  rw [weylUnit_val P hij]
  calc (1 - fUnit P i i - fUnit P j j - fUnit P i j + fUnit P j i) * fUnit P a b
      = fUnit P a b - fUnit P i i * fUnit P a b - fUnit P j j * fUnit P a b
          - fUnit P i j * fUnit P a b + fUnit P j i * fUnit P a b := by
        noncomm_ring
    _ = fUnit P a b := by rw [e1, e2, e3, e4]; abel

/-- `w_{ij}` carries `f_{ib}` to `f_{jb}` on the left. -/
theorem weyl_mul_fUnit_left (hij : i ≠ j) (b : ℕ) :
    ((weylUnit P hij : Rˣ) : R) * fUnit P i b = fUnit P j b := by
  have e1 : fUnit P i i * fUnit P i b = fUnit P i b := fUnit_mul_of_eq P i i b
  have e2 : fUnit P j j * fUnit P i b = 0 := fUnit_mul_of_ne P j b (Ne.symm hij)
  have e3 : fUnit P i j * fUnit P i b = 0 := fUnit_mul_of_ne P i b (Ne.symm hij)
  have e4 : fUnit P j i * fUnit P i b = fUnit P j b := fUnit_mul_of_eq P j i b
  rw [weylUnit_val P hij]
  calc (1 - fUnit P i i - fUnit P j j - fUnit P i j + fUnit P j i) * fUnit P i b
      = fUnit P i b - fUnit P i i * fUnit P i b - fUnit P j j * fUnit P i b
          - fUnit P i j * fUnit P i b + fUnit P j i * fUnit P i b := by
        noncomm_ring
    _ = fUnit P j b := by rw [e1, e2, e3, e4]; abel

/-- `w_{ij}^{-1}` fixes `f_{ab}` on the right when `b ∉ {i,j}`. -/
theorem fUnit_mul_weylInv_of_ne (hij : i ≠ j) (a : ℕ) {b : ℕ}
    (hbi : b ≠ i) (hbj : b ≠ j) :
    fUnit P a b * (((weylUnit P hij)⁻¹ : Rˣ) : R) = fUnit P a b := by
  have e1 : fUnit P a b * fUnit P i i = 0 := fUnit_mul_of_ne P a i hbi
  have e2 : fUnit P a b * fUnit P j j = 0 := fUnit_mul_of_ne P a j hbj
  have e3 : fUnit P a b * fUnit P i j = 0 := fUnit_mul_of_ne P a j hbi
  have e4 : fUnit P a b * fUnit P j i = 0 := fUnit_mul_of_ne P a i hbj
  rw [weylUnit_inv_val P hij]
  calc fUnit P a b * (1 - fUnit P i i - fUnit P j j + fUnit P i j - fUnit P j i)
      = fUnit P a b - fUnit P a b * fUnit P i i - fUnit P a b * fUnit P j j
          + fUnit P a b * fUnit P i j - fUnit P a b * fUnit P j i := by
        noncomm_ring
    _ = fUnit P a b := by rw [e1, e2, e3, e4]; abel

/-- `w_{ij}^{-1}` carries `f_{ai}` to `f_{aj}` on the right. -/
theorem fUnit_mul_weylInv_right (hij : i ≠ j) (a : ℕ) :
    fUnit P a i * (((weylUnit P hij)⁻¹ : Rˣ) : R) = fUnit P a j := by
  have e1 : fUnit P a i * fUnit P i i = fUnit P a i := fUnit_mul_of_eq P a i i
  have e2 : fUnit P a i * fUnit P j j = 0 := fUnit_mul_of_ne P a j hij
  have e3 : fUnit P a i * fUnit P i j = fUnit P a j := fUnit_mul_of_eq P a i j
  have e4 : fUnit P a i * fUnit P j i = 0 := fUnit_mul_of_ne P a i hij
  rw [weylUnit_inv_val P hij]
  calc fUnit P a i * (1 - fUnit P i i - fUnit P j j + fUnit P i j - fUnit P j i)
      = fUnit P a i - fUnit P a i * fUnit P i i - fUnit P a i * fUnit P j j
          + fUnit P a i * fUnit P i j - fUnit P a i * fUnit P j i := by
        noncomm_ring
    _ = fUnit P a j := by rw [e1, e2, e3, e4]; abel

end Weyl

/-! ## The printed conjugator `r = w_{14}w_{25}` -/

section Conjugator

variable (P : OneSidedInverse R)

theorem one_ne_four : (1 : ℕ) ≠ 4 := by decide

theorem two_ne_five : (2 : ℕ) ≠ 5 := by decide

/-- **Printed:** `r = w_{14}w_{25}`. -/
def rUnit : Rˣ := weylUnit P one_ne_four * weylUnit P two_ne_five

theorem rUnit_val :
    ((rUnit P : Rˣ) : R) =
      ((weylUnit P (one_ne_four) : Rˣ) : R) *
        ((weylUnit P (two_ne_five) : Rˣ) : R) := rfl

theorem rUnit_inv_val :
    (((rUnit P)⁻¹ : Rˣ) : R) =
      (((weylUnit P (two_ne_five))⁻¹ : Rˣ) : R) *
        (((weylUnit P (one_ne_four))⁻¹ : Rˣ) : R) := by
  rw [rUnit, mul_inv_rev]
  rfl

/-- `r f_{02} = f_{02}`: neither `1,4` nor `2,5` meets the left index `0`. -/
theorem rUnit_mul_fUnit_zero_two :
    ((rUnit P : Rˣ) : R) * fUnit P 0 2 = fUnit P 0 2 := by
  rw [rUnit_val, mul_assoc,
    weyl_mul_fUnit_of_ne P two_ne_five 2 (by decide) (by decide),
    weyl_mul_fUnit_of_ne P one_ne_four 2 (by decide) (by decide)]

/-- `f_{02} r^{-1} = f_{05}`: the right index `2` is carried to `5`, and `5`
misses `1,4`. -/
theorem fUnit_zero_two_mul_rUnit_inv :
    fUnit P 0 2 * (((rUnit P)⁻¹ : Rˣ) : R) = fUnit P 0 5 := by
  rw [rUnit_inv_val, ← mul_assoc,
    fUnit_mul_weylInv_right P two_ne_five 0,
    fUnit_mul_weylInv_of_ne P one_ne_four 0 (by decide) (by decide)]

/-- **Printed:** `r f_{02} r^{-1} = f_{05}`. -/
theorem rUnit_conj_fUnit_zero_two :
    ((rUnit P : Rˣ) : R) * fUnit P 0 2 * (((rUnit P)⁻¹ : Rˣ) : R) = fUnit P 0 5 := by
  rw [rUnit_mul_fUnit_zero_two, fUnit_zero_two_mul_rUnit_inv]

/-- `r f_{12} = f_{42}`: the left index `1` is carried to `4` by `w_{14}`, and
`w_{25}` misses it. -/
theorem rUnit_mul_fUnit_one_two :
    ((rUnit P : Rˣ) : R) * fUnit P 1 2 = fUnit P 4 2 := by
  rw [rUnit_val, mul_assoc,
    weyl_mul_fUnit_of_ne P two_ne_five 2 (by decide) (by decide),
    weyl_mul_fUnit_left P one_ne_four 2]

/-- `f_{42} r^{-1} = f_{45}`. -/
theorem fUnit_four_two_mul_rUnit_inv :
    fUnit P 4 2 * (((rUnit P)⁻¹ : Rˣ) : R) = fUnit P 4 5 := by
  rw [rUnit_inv_val, ← mul_assoc,
    fUnit_mul_weylInv_right P two_ne_five 4,
    fUnit_mul_weylInv_of_ne P one_ne_four 4 (by decide) (by decide)]

/-- **Printed:** `r f_{12} r^{-1} = f_{45}`. -/
theorem rUnit_conj_fUnit_one_two :
    ((rUnit P : Rˣ) : R) * fUnit P 1 2 * (((rUnit P)⁻¹ : Rˣ) : R) = fUnit P 4 5 := by
  rw [rUnit_mul_fUnit_one_two, fUnit_four_two_mul_rUnit_inv]

/-! ### The two `t^3` identities -/

/-- **Printed:** `f_{02}t^3 = f_{05}`. -/
theorem fUnit_zero_two_mul_t_cube :
    fUnit P 0 2 * P.t ^ 3 = fUnit P 0 5 := by
  simp only [fUnit]
  rw [mul_assoc, ← pow_add]

/-- **Printed:** `t^3 f_{45} = f_{12}t^3`. -/
theorem t_cube_mul_fUnit_four_five :
    P.t ^ 3 * fUnit P 4 5 = fUnit P 1 2 * P.t ^ 3 := by
  have hleft : P.t ^ 3 * fUnit P 4 5 = P.s * P.e * P.t ^ 5 := by
    simp only [fUnit]
    calc P.t ^ 3 * (P.s ^ 4 * P.e * P.t ^ 5)
        = (P.t ^ 3 * P.s ^ 3) * (P.s * P.e * P.t ^ 5) := by
          rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, pow_one]; noncomm_ring
      _ = P.s * P.e * P.t ^ 5 := by
          rw [OneSidedInverse.t_pow_mul_s_pow P 3, one_mul]
  have hright : fUnit P 1 2 * P.t ^ 3 = P.s * P.e * P.t ^ 5 := by
    simp only [fUnit, pow_one]
    rw [mul_assoc, ← pow_add]
  rw [hleft, hright]

end Conjugator

end TorsionComplementaryIdempotents
end OneSidedMFRadical
end Manuscript
end GroupApproximation
