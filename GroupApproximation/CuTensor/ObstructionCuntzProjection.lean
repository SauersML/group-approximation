import GroupApproximation.CuTensor.CuntzSubequiv
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Cuntz subequivalence of projections is Murray--von Neumann subequivalence

For projections `p`, `q` in a unital C-star algebra, `CuntzLE p q` gives a projection `e` below
`q` (`q e = e`) that is Murray--von Neumann equivalent to `p`.  This is the converse of
`cuntzLE_of_murrayVonNeumannEquiv` together with `cuntzLE_of_mul_eq`, and it is the step that lets
the classes of projections in the Cuntz semigroup see Murray--von Neumann equivalence.

## The proof

Pick `r` with `‖r q r* - p‖ < 1` and put `x = p r q`.  Then `x x* = p (r q r*) p`, so

    ‖p - x x*‖ = ‖p (p - r q r*) p‖ < 1.

The element `a = x x* + (1 - p)` is positive, and `1 - a = p - x x*`, so `a` is invertible.
It commutes with `p`, because `a p = p a = x x*`.  Let `b = a^(-1/2)`.  It is self-adjoint, satisfies
`b b a = a b b = 1`, and commutes with `a` and with `p`, since it is a continuous function of `a`.
The element `w = x* b` then satisfies

    w* w = b (x x*) b = b (a p) b = (b b a) p = p,

and `e = w w* = x* b b x` is a projection with `q e = e`.

## Main results

* `exists_murrayVonNeumannEquiv_le_of_cuntzLE`.
-/

namespace GroupApproximation
namespace CuTensor

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Cuntz subequivalence of projections gives Murray--von Neumann subequivalence.**  If `p` and
`q` are projections with `CuntzLE p q`, then some projection `e` with `q e = e` is Murray--von
Neumann equivalent to `p`. -/
theorem exists_murrayVonNeumannEquiv_le_of_cuntzLE {p q : A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (h : CuntzLE p q) :
    ∃ e : A, IsStarProjection e ∧ q * e = e ∧ MurrayVonNeumannEquiv p e := by
  obtain ⟨r, hr⟩ := h 1 one_pos
  have hp2 : p * p = p := hp.isIdempotentElem.eq
  have hq2 : q * q = q := hq.isIdempotentElem.eq
  have hps : star p = p := hp.isSelfAdjoint.star_eq
  have hqs : star q = q := hq.isSelfAdjoint.star_eq
  have hqq : ∀ y : A, q * (q * y) = q * y := fun y => by rw [← mul_assoc, hq2]
  -- The element `x = p r q` and its support relations.
  obtain ⟨x, hxdef⟩ : ∃ x : A, x = p * (r * q) := ⟨_, rfl⟩
  have hxs : star x = q * (star r * p) := by
    rw [hxdef, star_mul, star_mul, hps, hqs, mul_assoc]
  have hpx : p * x = x := by rw [hxdef, ← mul_assoc, hp2]
  have hxsp : star x * p = star x := by rw [hxs, mul_assoc, mul_assoc, hp2]
  have hqxs : q * star x = star x := by rw [hxs, ← mul_assoc, hq2]
  -- `x x*` is close to `p`.
  obtain ⟨d, hddef⟩ : ∃ d : A, d = r * q * star r := ⟨_, rfl⟩
  have hxx : x * star x = p * d * p := by
    rw [hxs, hxdef, hddef]
    simp only [mul_assoc, hqq]
  have hsub : p - x * star x = p * (p - d) * p := by
    rw [hxx, mul_sub, sub_mul, hp2, hp2]
  have hpn : ‖p‖ ≤ 1 := IsStarProjection.norm_le p hp
  have hd : ‖p - d‖ < 1 := by rw [norm_sub_rev, hddef]; exact hr
  have hnorm : ‖p - x * star x‖ < 1 := by
    rw [hsub]
    calc ‖p * (p - d) * p‖ ≤ ‖p * (p - d)‖ * ‖p‖ := norm_mul_le _ _
      _ ≤ ‖p * (p - d)‖ := mul_le_of_le_one_right (norm_nonneg _) hpn
      _ ≤ ‖p‖ * ‖p - d‖ := norm_mul_le _ _
      _ ≤ ‖p - d‖ := mul_le_of_le_one_left (norm_nonneg _) hpn
      _ < 1 := hd
  -- The invertible positive element `a = x x* + (1 - p)`, which commutes with `p`.
  obtain ⟨a, hadef⟩ : ∃ a : A, a = x * star x + (1 - p) := ⟨_, rfl⟩
  have haunit : IsUnit a := by
    have h1 : a = 1 - (p - x * star x) := by rw [hadef]; abel
    rw [h1]
    exact isUnit_one_sub_of_norm_lt_one hnorm
  have hanonneg : (0 : A) ≤ a := by
    have h1p : 1 - p = (1 - p) * star (1 - p) := by
      rw [hp.one_sub.isSelfAdjoint.star_eq, hp.one_sub.isIdempotentElem.eq]
    rw [hadef, h1p]
    exact add_nonneg (mul_star_self_nonneg x) (mul_star_self_nonneg _)
  have hap1 : a * p = x * star x := by
    rw [hadef, add_mul, hp.one_sub_mul_self, add_zero, mul_assoc, hxsp]
  have hpa1 : p * a = x * star x := by
    rw [hadef, mul_add, hp.mul_one_sub_self, add_zero, ← mul_assoc, hpx]
  have hap : Commute a p := (commute_iff_eq _ _).mpr (hap1.trans hpa1.symm)
  -- The inverse square root `b = a^(-1/2)`.
  have hasp : IsStrictlyPositive a := haunit.isStrictlyPositive hanonneg
  obtain ⟨b, hbdef⟩ : ∃ b : A, b = a ^ (-(2⁻¹) : ℝ) := ⟨_, rfl⟩
  have hbnonneg : (0 : A) ≤ b := by rw [hbdef]; exact CFC.rpow_nonneg
  have hbs : star b = b := hbnonneg.star_eq
  have hexp : (-(2⁻¹) : ℝ) + (-(2⁻¹) : ℝ) = -(1 : ℝ) := by norm_num
  have hbb : b * b = a ^ (-(1 : ℝ)) := by rw [hbdef, ← CFC.rpow_add haunit, hexp]
  have hab : a * (b * b) = 1 := by
    have h1 := CFC.rpow_mul_rpow_neg (a := a) 1 hasp
    rw [CFC.rpow_one a hanonneg] at h1
    rw [hbb]; exact h1
  have hba : b * b * a = 1 := by
    have h1 := CFC.rpow_neg_mul_rpow (a := a) 1 hasp
    rw [CFC.rpow_one a hanonneg] at h1
    rw [hbb]; exact h1
  have hcab : Commute a b := by
    rw [hbdef, CFC.rpow_def]; exact (Commute.cfc_nnreal (Commute.refl a) _).symm
  have hbp : Commute b p := by rw [hbdef, CFC.rpow_def]; exact Commute.cfc_nnreal hap _
  -- The partial isometry `w = x* b` and the projection `e = w w*`.
  have hxxs' : ∀ y : A, x * (star x * y) = p * (a * y) := fun y => by
    rw [← mul_assoc, ← hpa1, mul_assoc]
  have habb : ∀ y : A, a * (b * (b * y)) = y := fun y => by
    rw [← mul_assoc b b y, ← mul_assoc, hab, one_mul]
  obtain ⟨e, hedef⟩ : ∃ e : A, e = star x * (b * (b * x)) := ⟨_, rfl⟩
  have hes : star e = e := by
    rw [hedef]
    simp only [star_mul, star_star, hbs, mul_assoc]
  have hee : e * e = e := by
    rw [hedef]
    simp only [mul_assoc]
    rw [hxxs', habb, hpx]
  have hqe : q * e = e := by rw [hedef, ← mul_assoc, hqxs]
  have hwsw : star (star x * b) * (star x * b) = p := by
    rw [star_mul, star_star, hbs]
    calc b * x * (star x * b) = b * (x * star x) * b := by simp only [mul_assoc]
      _ = b * (a * p) * b := by rw [hap1]
      _ = b * (a * (b * p)) := by rw [mul_assoc, mul_assoc, hbp.symm.eq]
      _ = b * (b * (a * p)) := by rw [hcab.left_comm]
      _ = p := by rw [← mul_assoc b a p, ← mul_assoc, ← mul_assoc, hba, one_mul]
  have hwws : star x * b * star (star x * b) = e := by
    rw [star_mul, star_star, hbs, hedef, mul_assoc]
  exact ⟨e, ⟨hee, hes⟩, hqe, ⟨star x * b, hwsw, hwws⟩⟩

end CuTensor
end GroupApproximation
