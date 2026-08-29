import GroupApproximation.Monsters.SL2BraidPresentation
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.LinearCombination

/-!
# The Möbius action of `SL₂(ℤ)` on the irrational reals

An integer matrix of determinant one acts on the real line by the
fractional-linear map `x ↦ (a x + b) / (c x + d)`.  On an irrational
argument the denominator never vanishes — a vanishing denominator would
display `x` as an integer ratio — and the value is again irrational,
because the inverse matrix transports a rational value back to a
rational argument.  The action is therefore a permutation representation

  `rep : SL₂(ℤ) →* Equiv.Perm Irr`

on the subtype `Irr` of irrational reals.  This is the classical
boundary action of the modular group; the completeness argument for the
rank-two braid presentation runs the Ping-Pong-Lemma through it on the
two half-lines.
-/

namespace GroupApproximation
namespace MoebiusIrrationalAction

open SL2BraidPresentation

noncomputable section

/-- The irrational reals. -/
abbrev Irr : Type := {x : ℝ // Irrational x}

/-- A matrix entry, as a real number. -/
abbrev ent (M : SL2) (i j : Fin 2) : ℝ :=
  ((M : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ)

/-- The fractional-linear value of a matrix at a real argument. -/
def moebiusVal (M : SL2) (x : ℝ) : ℝ :=
  (ent M 0 0 * x + ent M 0 1) / (ent M 1 0 * x + ent M 1 1)

/-! ## Nonvanishing and irrationality -/

private theorem lin_ne_zero {c d : ℤ} (h : ¬(c = 0 ∧ d = 0)) {x : ℝ}
    (hx : Irrational x) : (c : ℝ) * x + (d : ℝ) ≠ 0 := by
  by_cases hc : c = 0
  · have hd0 : d ≠ 0 := fun hd0 => h ⟨hc, hd0⟩
    rw [hc]
    intro hzero
    apply hd0
    have hcast : (d : ℝ) = 0 := by simpa using hzero
    exact_mod_cast hcast
  · intro hzero
    apply hx.ne_rational (-d) c
    have hc' : (c : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hc
    rw [eq_div_iff hc']
    push_cast
    linarith only [hzero]

private theorem bottom_row_ne_zero (M : SL2) :
    ¬((M : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 ∧
      (M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 0) := by
  rintro ⟨h0, h1⟩
  have hd : (M : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := M.property
  rw [Matrix.det_fin_two, h0, h1] at hd
  simp at hd

/-- The denominator of the fractional-linear map never vanishes at an
irrational argument. -/
theorem den_ne_zero (M : SL2) {x : ℝ} (hx : Irrational x) :
    ent M 1 0 * x + ent M 1 1 ≠ 0 :=
  lin_ne_zero (bottom_row_ne_zero M) hx

private theorem det_ent (M : SL2) :
    (M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (M : Matrix (Fin 2) (Fin 2) ℤ) 1 0
      = 1 := by
  have hd : (M : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := M.property
  rwa [Matrix.det_fin_two] at hd

/-- The fractional-linear value at an irrational argument is
irrational. -/
theorem moebiusVal_irrational (M : SL2) {x : ℝ} (hx : Irrational x) :
    Irrational (moebiusVal M x) := by
  set a : ℤ := (M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  set b : ℤ := (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
  set c : ℤ := (M : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc
  set d : ℤ := (M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd
  have hdet : a * d - b * c = 1 := det_ent M
  have hden : (c : ℝ) * x + (d : ℝ) ≠ 0 := den_ne_zero M hx
  intro hy
  obtain ⟨q, hq⟩ := hy
  set y : ℝ := moebiusVal M x with hy'
  have hclear : y * ((c : ℝ) * x + d) = (a : ℝ) * x + b := by
    rw [hy']
    show ((a : ℝ) * x + b) / ((c : ℝ) * x + d) * ((c : ℝ) * x + d) =
      (a : ℝ) * x + b
    exact div_mul_cancel₀ _ hden
  have hdetR : (a : ℝ) * d - b * c = 1 := by exact_mod_cast hdet
  have hden2 : (a : ℝ) - (c : ℝ) * y ≠ 0 := by
    intro hzero
    have hay : (a : ℝ) = c * y := by linarith only [hzero]
    have hby : (d : ℝ) * y = b := by linear_combination hclear + x * hay
    have hcontra : (0 : ℝ) = 1 := by
      linear_combination hdetR - d * hay - c * hby
    exact absurd hcontra (by norm_num)
  have hx' : x * ((a : ℝ) - c * y) = (d : ℝ) * y - b := by
    linear_combination -hclear
  apply hx
  refine ⟨((d : ℚ) * q - b) / ((a : ℚ) - c * q), ?_⟩
  have hcast : ((((d : ℚ) * q - b) / ((a : ℚ) - c * q) : ℚ) : ℝ) =
      ((d : ℝ) * y - b) / ((a : ℝ) - c * y) := by
    push_cast
    rw [hq]
  rw [hcast, div_eq_iff hden2]
  linear_combination -hx'

/-! ## The permutation representation -/

/-- The Möbius action on the irrational subtype. -/
def moebius (M : SL2) (x : Irr) : Irr :=
  ⟨moebiusVal M x.1, moebiusVal_irrational M x.2⟩

theorem moebiusVal_one (x : ℝ) : moebiusVal 1 x = x := by
  simp [moebiusVal, ent, Matrix.SpecialLinearGroup.coe_one]

theorem moebiusVal_mul (M N : SL2) {x : ℝ} (hx : Irrational x) :
    moebiusVal M (moebiusVal N x) = moebiusVal (M * N) x := by
  have hdN := den_ne_zero N hx
  have hyirr := moebiusVal_irrational N hx
  have hdM := den_ne_zero M hyirr
  have hdMN := den_ne_zero (M * N) hx
  have hMN : ∀ i j : Fin 2, ent (M * N) i j =
      ent M i 0 * ent N 0 j + ent M i 1 * ent N 1 j := by
    intro i j
    show (((M * N : SL2) : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ) = _
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
    push_cast
    ring
  rw [hMN 1 0, hMN 1 1] at hdMN
  show (ent M 0 0 * moebiusVal N x + ent M 0 1) /
      (ent M 1 0 * moebiusVal N x + ent M 1 1) =
    (ent (M * N) 0 0 * x + ent (M * N) 0 1) /
      (ent (M * N) 1 0 * x + ent (M * N) 1 1)
  rw [hMN 0 0, hMN 0 1, hMN 1 0, hMN 1 1]
  rw [div_eq_div_iff hdM hdMN]
  have hdN' : x * ent N 1 0 + ent N 1 1 ≠ 0 := by
    intro hzero
    apply hdN
    linear_combination hzero
  unfold moebiusVal
  field_simp [hdN']
  ring

theorem moebius_mul (M N : SL2) (x : Irr) :
    moebius M (moebius N x) = moebius (M * N) x :=
  Subtype.ext (moebiusVal_mul M N x.2)

theorem moebius_one (x : Irr) : moebius 1 x = x :=
  Subtype.ext (moebiusVal_one x.1)

/-- The Möbius permutation of the irrationals attached to a
determinant-one integer matrix. -/
def moebiusPerm (M : SL2) : Equiv.Perm Irr where
  toFun := moebius M
  invFun := moebius M⁻¹
  left_inv x := by rw [moebius_mul, inv_mul_cancel, moebius_one]
  right_inv x := by rw [moebius_mul, mul_inv_cancel, moebius_one]

/-- The permutation representation of `SL₂(ℤ)` on the irrationals. -/
def rep : SL2 →* Equiv.Perm Irr where
  toFun := moebiusPerm
  map_one' := Equiv.ext fun x => moebius_one x
  map_mul' M N := Equiv.ext fun x => by
    simp only [Equiv.Perm.mul_apply]
    exact (moebius_mul M N x).symm

end

end MoebiusIrrationalAction
end GroupApproximation
