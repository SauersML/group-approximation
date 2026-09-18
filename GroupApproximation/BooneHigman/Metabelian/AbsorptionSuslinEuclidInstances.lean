import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidStep
import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinTransport
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin input, part 4: Euclidean domains and `ℤ[1/m]`

Lane `bh-met-23`.  Instances of `HasWellFoundedDivision`, and with them `SL_N = E_N`:

* every Euclidean domain (`hasWellFoundedDivision_of_euclideanDomain`), in particular
  `F_p[X]` (`specialLinearInElementary_zmodPolynomial`);
* `ℤ[1/m]` for **every** `m`, including `m = 0` (the zero ring) and `m = 1` (`ℤ`), with no case
  split (`hasWellFoundedDivision_away`).  The size of `z` is the least `|c|` over all
  representations `z · m^i = c`; dividing a representative `d` of `a m^j` by the minimal
  representative `c` of `b` in `ℤ`, the quotient `q = (d / c) m^i m^{-j}` leaves the remainder
  `a - b q = (d % c) m^{-j}`, whose size is at most `|d % c| < |c|`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

/-- Every Euclidean domain has a well-founded division with remainder. -/
theorem hasWellFoundedDivision_of_euclideanDomain (R : Type*) [EuclideanDomain R] :
    HasWellFoundedDivision R :=
  ⟨EuclideanDomain.r, EuclideanDomain.r_wellFounded, fun a b hb ↦ ⟨a / b, by
    rw [← eq_sub_of_add_eq' (EuclideanDomain.div_add_mod a b)]
    exact EuclideanDomain.mod_lt a hb⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.hasWellFoundedDivision_of_euclideanDomain

/-- `SL_N(F_p[X]) = E_N(F_p[X])` at every positive rank. -/
theorem specialLinearInElementary_zmodPolynomial (p : ℕ) [Fact p.Prime] {N : ℕ} (hN : 0 < N) :
    SpecialLinearInElementary (Polynomial (ZMod p)) N :=
  specialLinearInElementary_of_hasWellFoundedDivision
    (hasWellFoundedDivision_of_euclideanDomain (Polynomial (ZMod p))) hN

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.specialLinearInElementary_zmodPolynomial

/-- The size of `z ∈ ℤ[1/m]`: the least `|c|` with `z · m^i = c` for some `i`. -/
noncomputable def suslinAwaySize (m : ℕ) (z : Localization.Away (m : ℤ)) : ℕ :=
  sInf {n : ℕ | ∃ (i : ℕ) (c : ℤ),
    z * algebraMap ℤ (Localization.Away (m : ℤ)) (m : ℤ) ^ i =
      algebraMap ℤ (Localization.Away (m : ℤ)) c ∧ c.natAbs = n}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinAwaySize

/-- The size is attained. -/
theorem suslinAwaySize_spec (m : ℕ) (z : Localization.Away (m : ℤ)) :
    ∃ (i : ℕ) (c : ℤ), z * algebraMap ℤ (Localization.Away (m : ℤ)) (m : ℤ) ^ i =
      algebraMap ℤ (Localization.Away (m : ℤ)) c ∧ c.natAbs = suslinAwaySize m z := by
  obtain ⟨i, c, h⟩ := IsLocalization.Away.surj (m : ℤ) z
  exact Nat.sInf_mem ⟨c.natAbs, i, c, h, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinAwaySize_spec

/-- The size is at most `|c|` for every representation `z · m^i = c`. -/
theorem suslinAwaySize_le (m : ℕ) {z : Localization.Away (m : ℤ)} {i : ℕ} {c : ℤ}
    (h : z * algebraMap ℤ (Localization.Away (m : ℤ)) (m : ℤ) ^ i =
      algebraMap ℤ (Localization.Away (m : ℤ)) c) :
    suslinAwaySize m z ≤ c.natAbs :=
  Nat.sInf_le ⟨i, c, h, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinAwaySize_le

/-- **`ℤ[1/m]` has a well-founded division with remainder**, for every `m`. -/
theorem hasWellFoundedDivision_away (m : ℕ) :
    HasWellFoundedDivision (Localization.Away (m : ℤ)) := by
  refine ⟨InvImage (· < ·) (suslinAwaySize m), InvImage.wf _ wellFounded_lt,
    fun a b hb ↦ ?_⟩
  obtain ⟨i, c, hbc, hcb⟩ := suslinAwaySize_spec m b
  obtain ⟨j, d, had⟩ := IsLocalization.Away.surj (m : ℤ) a
  have hc : c ≠ 0 := by
    rintro rfl
    rw [map_zero, IsUnit.mul_left_eq_zero
      (IsLocalization.Away.algebraMap_pow_isUnit (S := Localization.Away (m : ℤ)) (m : ℤ) i)]
      at hbc
    exact hb hbc
  obtain ⟨u, hu⟩ :=
    IsLocalization.Away.algebraMap_pow_isUnit (S := Localization.Away (m : ℤ)) (m : ℤ) j
  have hu1 : ((u⁻¹ : (Localization.Away (m : ℤ))ˣ) : Localization.Away (m : ℤ)) *
      algebraMap ℤ (Localization.Away (m : ℤ)) (m : ℤ) ^ j = 1 := by
    rw [← hu, Units.inv_mul]
  have hdr : c * (d / c) + d % c = d := Int.mul_ediv_add_emod d c
  have hkey : (a - b * (algebraMap ℤ (Localization.Away (m : ℤ)) (d / c) *
      algebraMap ℤ (Localization.Away (m : ℤ)) (m : ℤ) ^ i *
        ((u⁻¹ : (Localization.Away (m : ℤ))ˣ) : Localization.Away (m : ℤ)))) *
      algebraMap ℤ (Localization.Away (m : ℤ)) (m : ℤ) ^ j =
        algebraMap ℤ (Localization.Away (m : ℤ)) (d % c) := by
    calc (a - b * (algebraMap ℤ (Localization.Away (m : ℤ)) (d / c) *
          algebraMap ℤ (Localization.Away (m : ℤ)) (m : ℤ) ^ i *
            ((u⁻¹ : (Localization.Away (m : ℤ))ˣ) : Localization.Away (m : ℤ)))) *
          algebraMap ℤ (Localization.Away (m : ℤ)) (m : ℤ) ^ j
        = a * algebraMap ℤ (Localization.Away (m : ℤ)) (m : ℤ) ^ j -
            (b * algebraMap ℤ (Localization.Away (m : ℤ)) (m : ℤ) ^ i) *
              algebraMap ℤ (Localization.Away (m : ℤ)) (d / c) *
              (((u⁻¹ : (Localization.Away (m : ℤ))ˣ) : Localization.Away (m : ℤ)) *
                algebraMap ℤ (Localization.Away (m : ℤ)) (m : ℤ) ^ j) := by ring
      _ = algebraMap ℤ (Localization.Away (m : ℤ)) d -
            algebraMap ℤ (Localization.Away (m : ℤ)) c *
              algebraMap ℤ (Localization.Away (m : ℤ)) (d / c) := by
        rw [had, hbc, hu1, mul_one]
      _ = algebraMap ℤ (Localization.Away (m : ℤ)) (d % c) := by
        have hr : d % c = d - c * (d / c) := by linear_combination hdr
        rw [hr, map_sub, map_mul]
  refine ⟨algebraMap ℤ (Localization.Away (m : ℤ)) (d / c) *
      algebraMap ℤ (Localization.Away (m : ℤ)) (m : ℤ) ^ i *
        ((u⁻¹ : (Localization.Away (m : ℤ))ˣ) : Localization.Away (m : ℤ)), ?_⟩
  show suslinAwaySize m _ < suslinAwaySize m b
  refine lt_of_le_of_lt (suslinAwaySize_le m hkey) ?_
  rw [← hcb, ← Int.natAbs_abs c]
  exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (Int.emod_nonneg d hc) (Int.emod_lt_abs d hc)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.hasWellFoundedDivision_away

/-- `SL_N(ℤ[1/m]) = E_N(ℤ[1/m])` at every positive rank, for every `m`. -/
theorem specialLinearInElementary_away (m : ℕ) {N : ℕ} (hN : 0 < N) :
    SpecialLinearInElementary (Localization.Away (m : ℤ)) N :=
  specialLinearInElementary_of_hasWellFoundedDivision (hasWellFoundedDivision_away m) hN

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.specialLinearInElementary_away

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
