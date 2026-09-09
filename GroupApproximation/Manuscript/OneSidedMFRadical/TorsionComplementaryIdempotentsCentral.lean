import GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotentsCell

/-!
# The printed central element `z` and the two commutators it kills

`non_mf_groups_exist.tex`, Proposition `prop:torsion-defect-ring`, the proof:

> So `d = [vcv^{-1}, ℓ] = e_{24}(-f_{02})` lies in `𝔇_B(L)`, and
> `[y,d] = D(1-f_{12}) = z^{-1}` since `f_{02}f_{10} = 0` and
> `f_{10}f_{02} = f_{12}`; hence `z ∈ 𝔇_B(L)`.  The element `z` commutes with
> `L` and `v`, and with `c` and `y` because
> `f_{12}f_{02} = f_{02}f_{12} = f_{12}f_{10} = 0`, so `⟨z⟩` is central in `B`.
> If `me = 0` then `z^m = D(1 + m f_{12}) = 1`, and `z ≠ 1` because
> `t f_{12} s^2 = e ≠ 0`. … Then
> `[z, e_{41}(f_{20})] = e_{41}(f_{10})`, `[e_{24}(t), e_{41}(f_{10})] = e_{21}(e)`
> are killed.

Every identity in that passage is proved here, at the level of `EL₄(R)` and
over a bare one-sided inverse pair.  The torsion hypothesis `m e = 0` is used
in exactly one declaration, `printedZ_pow_eq_one`, and `e ≠ 0` in exactly one,
`printedZ_ne_one`.

The two displayed commutators are the printed bridge from `z` to the ideal:
whatever kills `z` kills `e_{21}(e)`, and `TorsionComplementaryIdempotentsIdeal`
turns that into `EL_n(R, ReR)`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TorsionComplementaryIdempotents

open GroupApproximation.OneSidedCompressor
open scoped commutatorElement

universe u

variable {R : Type u} [Ring R]

/-! ## Two specialisations of `D(a)` against a single elementary matrix -/

/-- `D(a)` multiplies the fourth row on the left. -/
theorem lastDiag_mul_single_last (a b : R) (q : Fin 4) :
    lastDiag a * Matrix.single lastIdx q b = Matrix.single lastIdx q (a * b) := by
  rw [lastDiag_mul_single]
  simp

/-- `D(a)` is invisible on the right of a column in the core. -/
theorem single_mul_lastDiag_core (a b : R) (p : Fin 4) (i : Fin 3) :
    Matrix.single p (coreIdx i) b * lastDiag a
      = Matrix.single p (coreIdx i) b := by
  rw [single_mul_lastDiag, if_neg (coreIdx_ne_last i), mul_one]

variable (P : OneSidedInverse R)

/-! ## The printed defect element `d = e_{24}(-f_{02})` -/

/-- **Printed:** `d = [vcv^{-1}, ℓ] = e_{24}(-f_{02})`, the Steinberg relation in
its `i = l` form. -/
theorem printedDefectElt_eq :
    ⁅elementaryRoot (coreIdx 0) lastIdx (coreIdx_ne_last 0) (fUnit P 0 2),
      printedEllTwoOne R⁆ = printedDefectElt P := by
  refine elementaryGroup_ext ?_
  have hXX : Matrix.single (coreIdx 0) lastIdx (fUnit P 0 2) *
      Matrix.single (coreIdx 0) lastIdx (fUnit P 0 2) = 0 :=
    Matrix.single_mul_single_of_ne (c := fUnit P 0 2) (coreIdx 0) lastIdx
      (coreIdx 0) (last_ne_coreIdx 0) (fUnit P 0 2)
  have hYY : Matrix.single (coreIdx 1) (coreIdx 0)
      (1 : R) * Matrix.single (coreIdx 1) (coreIdx 0) (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : R)) (coreIdx 1) (coreIdx 0)
      (coreIdx 1) (coreIdx_injective.ne (Ne.symm oneNeZeroFin)) 1
  have hXY : Matrix.single (coreIdx 0) lastIdx (fUnit P 0 2) *
      Matrix.single (coreIdx 1) (coreIdx 0) (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (c := fUnit P 0 2) (coreIdx 0) lastIdx
      (coreIdx 1) (last_ne_coreIdx 1) 1
  have hYX : Matrix.single (coreIdx 1) (coreIdx 0) (1 : R) *
      Matrix.single (coreIdx 0) lastIdx (fUnit P 0 2)
      = Matrix.single (coreIdx 1) lastIdx (fUnit P 0 2) := by
    rw [Matrix.single_mul_single_same, one_mul]
  show (1 + Matrix.single (coreIdx 0) lastIdx (fUnit P 0 2)) *
      (1 + Matrix.single (coreIdx 1) (coreIdx 0) (1 : R)) *
      (1 - Matrix.single (coreIdx 0) lastIdx (fUnit P 0 2)) *
      (1 - Matrix.single (coreIdx 1) (coreIdx 0) (1 : R))
    = 1 + Matrix.single (coreIdx 1) lastIdx (-fUnit P 0 2)
  rw [commutator_of_mul_eq_zero hXX hYY hXY, hYX, ← Matrix.single_neg]
  abel

/-! ## `[y, d] = z^{-1}` -/

/-- **Printed:** `[y,d] = D(1-f_{12}) = z^{-1}`, from `f_{02}f_{10} = 0` and
`f_{10}f_{02} = f_{12}`. -/
theorem printedY_printedDefectElt_commutator :
    ⁅printedY P, printedDefectElt P⁆ = (printedZ P)⁻¹ := by
  have hyx : (-fUnit P 0 2) * fUnit P 1 0 = 0 := by
    rw [neg_mul, fUnit_mul_of_ne P 0 0 (by decide : (2 : ℕ) ≠ 1), neg_zero]
  have hval : ((⁅printedY P, printedDefectElt P⁆ :
        elementaryGroup (Fin 4) R) : (Matrix (Fin 4) (Fin 4) R)ˣ)
      = lastDiag (1 + fUnit P 1 0 * (-fUnit P 0 2)) :=
    commutator_last_eq_lastDiag (last_ne_coreIdx 1) hyx
  have hxy : fUnit P 1 0 * (-fUnit P 0 2) = -fUnit P 1 2 := by
    rw [mul_neg, fUnit_mul_of_eq P 1 0 2]
  rw [hxy] at hval
  refine eq_inv_of_mul_eq_one_left (elementaryGroup_ext ?_)
  rw [elementaryGroup_val_mul, hval, printedZ_matrix P, lastDiag_mul]
  have hprod : (1 + -fUnit P 1 2) * (1 + fUnit P 1 2) = 1 := by
    have hsq : fUnit P 1 2 * fUnit P 1 2 = 0 :=
      fUnit_mul_self P (by decide : (1 : ℕ) ≠ 2)
    calc (1 + -fUnit P 1 2) * (1 + fUnit P 1 2)
        = 1 - fUnit P 1 2 * fUnit P 1 2 := by noncomm_ring
      _ = 1 := by rw [hsq, sub_zero]
  rw [hprod, lastDiag_one]
  rfl

/-! ## `⟨z⟩` is central in `B = ⟨L, v, c, y⟩` -/

/-- `z` commutes with `v`: the printed `v z v^{-1} = z`. -/
theorem printedZ_commute_printedV : Commute (printedZ P) (printedV P) := by
  have h := printedV_conj_printedZ P
  have : printedV P * printedZ P = printedZ P * printedV P := by
    calc printedV P * printedZ P
        = printedV P * printedZ P * (printedV P)⁻¹ * printedV P := by group
      _ = printedZ P * printedV P := by rw [h]
  exact this.symm

/-- `z` commutes with `c`, because `f_{12}f_{02} = f_{02}f_{12} = 0`. -/
theorem printedZ_commute_printedC : Commute (printedZ P) (printedC P) := by
  refine elementaryGroup_ext ?_
  rw [elementaryGroup_val_mul, elementaryGroup_val_mul, printedZ_matrix P,
    printedC_matrix P, lastDiag_mul, lastDiag_mul]
  have h1 : fUnit P 1 2 * fUnit P 0 2 = 0 :=
    fUnit_mul_of_ne P 1 2 (by decide : (2 : ℕ) ≠ 0)
  have h2 : fUnit P 0 2 * fUnit P 1 2 = 0 :=
    fUnit_mul_of_ne P 0 2 (by decide : (2 : ℕ) ≠ 1)
  congr 1
  calc (1 + fUnit P 1 2) * (1 + fUnit P 0 2)
      = 1 + fUnit P 1 2 + fUnit P 0 2 + fUnit P 1 2 * fUnit P 0 2 := by
        noncomm_ring
    _ = 1 + fUnit P 1 2 + fUnit P 0 2 := by rw [h1, add_zero]
    _ = 1 + fUnit P 0 2 + fUnit P 1 2 + fUnit P 0 2 * fUnit P 1 2 := by
        rw [h2]; abel
    _ = (1 + fUnit P 0 2) * (1 + fUnit P 1 2) := by noncomm_ring

/-- `z` commutes with `y`, because `f_{12}f_{10} = 0`. -/
theorem printedZ_commute_printedY : Commute (printedZ P) (printedY P) := by
  refine elementaryGroup_ext ?_
  rw [elementaryGroup_val_mul, elementaryGroup_val_mul, printedZ_matrix P,
    printedY, elementaryRoot_matrix]
  have h : fUnit P 1 2 * fUnit P 1 0 = 0 :=
    fUnit_mul_of_ne P 1 0 (by decide : (2 : ℕ) ≠ 1)
  have hleft : (1 + fUnit P 1 2) * fUnit P 1 0 = fUnit P 1 0 := by
    rw [add_mul, one_mul, h, add_zero]
  rw [mul_add, mul_one, add_mul, one_mul, lastDiag_mul_single_last,
    single_mul_lastDiag_core, hleft]

/-! ## The order of `z` -/

/-- **Printed:** if `m e = 0` then `z^m = D(1 + m f_{12}) = 1`. -/
theorem printedZ_pow_eq_one {m : ℕ} (h : m • P.e = 0) : printedZ P ^ m = 1 := by
  have hsq : fUnit P 1 2 * fUnit P 1 2 = 0 :=
    fUnit_mul_self P (by decide : (1 : ℕ) ≠ 2)
  refine elementaryGroup_ext ?_
  rw [elementaryGroup_val_pow, printedZ_matrix P, lastDiag_pow,
    one_add_pow_of_sq_zero hsq m, nsmul_fUnit P h 1 2, add_zero, lastDiag_one]
  rfl

/-- **Printed:** `z ≠ 1`, because `t f_{12} s^2 = e ≠ 0`. -/
theorem printedZ_ne_one (he : P.e ≠ 0) : printedZ P ≠ 1 := by
  intro hz
  have hmat : lastDiag (1 + fUnit P 1 2) = (1 : Matrix (Fin 4) (Fin 4) R) := by
    rw [← printedZ_matrix P, hz]
    rfl
  have hentry := congrFun (congrFun hmat lastIdx) lastIdx
  rw [lastDiag, Matrix.diagonal_apply_eq, if_pos rfl, Matrix.one_apply_eq]
    at hentry
  have : fUnit P 1 2 = 0 := by
    have := hentry
    linear_combination (norm := abel) this
  exact fUnit_one_two_ne_zero P he this

/-! ## The two printed commutators after `z` -/

/-- **Printed:** `[z, e_{41}(f_{20})] = e_{41}(f_{10})`. -/
theorem printedZ_commutator_root :
    ⁅printedZ P,
      elementaryRoot lastIdx (coreIdx 0) (last_ne_coreIdx 0) (fUnit P 2 0)⁆
      = elementaryRoot lastIdx (coreIdx 0) (last_ne_coreIdx 0) (fUnit P 1 0) := by
  have hmul : fUnit P 1 2 * fUnit P 2 0 = fUnit P 1 0 := fUnit_mul_of_eq P 1 2 0
  have key : printedZ P *
      elementaryRoot lastIdx (coreIdx 0) (last_ne_coreIdx 0) (fUnit P 2 0)
      = elementaryRoot lastIdx (coreIdx 0) (last_ne_coreIdx 0)
          (fUnit P 2 0 + fUnit P 1 0) * printedZ P := by
    refine elementaryGroup_ext ?_
    rw [elementaryGroup_val_mul, elementaryGroup_val_mul, printedZ_matrix P,
      elementaryRoot_matrix, elementaryRoot_matrix, mul_add, mul_one, add_mul,
      one_mul, lastDiag_mul_single_last, single_mul_lastDiag_core]
    have hleft : (1 + fUnit P 1 2) * fUnit P 2 0 = fUnit P 2 0 + fUnit P 1 0 := by
      rw [add_mul, one_mul, hmul]
    rw [hleft]
  rw [commutatorElement_def, key]
  calc elementaryRoot lastIdx (coreIdx 0) (last_ne_coreIdx 0)
        (fUnit P 2 0 + fUnit P 1 0) * printedZ P * (printedZ P)⁻¹ *
        (elementaryRoot lastIdx (coreIdx 0) (last_ne_coreIdx 0) (fUnit P 2 0))⁻¹
      = elementaryRoot lastIdx (coreIdx 0) (last_ne_coreIdx 0)
          (fUnit P 2 0 + fUnit P 1 0) *
          (elementaryRoot lastIdx (coreIdx 0) (last_ne_coreIdx 0)
            (fUnit P 2 0))⁻¹ := by group
    _ = elementaryRoot lastIdx (coreIdx 0) (last_ne_coreIdx 0) (fUnit P 1 0) := by
        rw [← elementaryRoot_neg, elementaryRoot_mul]
        congr 1
        abel

/-- **Printed:** `[e_{24}(t), e_{41}(f_{10})] = e_{21}(e)`, since
`t f_{10} = t s e = e`. -/
theorem printedT_commutator_root :
    ⁅elementaryRoot (coreIdx 1) lastIdx (coreIdx_ne_last 1) P.t,
      elementaryRoot lastIdx (coreIdx 0) (last_ne_coreIdx 0) (fUnit P 1 0)⁆
      = elementaryRoot (coreIdx 1) (coreIdx 0)
          (coreIdx_injective.ne oneNeZeroFin) P.e := by
  have hmul : P.t * fUnit P 1 0 = P.e := by
    rw [fUnit, pow_one, pow_zero, mul_one, ← mul_assoc, P.t_mul_s, one_mul]
  rw [elementaryRoot_commutator (coreIdx 1) lastIdx (coreIdx 0)
    (coreIdx_ne_last 1) (last_ne_coreIdx 0)
    (coreIdx_injective.ne oneNeZeroFin) P.t (fUnit P 1 0), hmul]

end TorsionComplementaryIdempotents
end OneSidedMFRadical
end Manuscript
end GroupApproximation
