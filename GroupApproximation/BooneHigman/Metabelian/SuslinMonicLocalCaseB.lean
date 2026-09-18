import GroupApproximation.BooneHigman.Metabelian.SuslinMonicLocalCaseA
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Local monic induction, case B: unit constant term in the first entry

Lane `bh-met-93i`.  `R` local, `(f, g)` a first row of `SL₂(R[X])` (`f k - g c = 1`),
`lc f = v ∈ Rˣ`, `deg f = n + 1`, `f(0) = e ∈ Rˣ`, `F = v⁻¹ f` monic.
* `f = e + X p` and `w = -e⁻¹ p` satisfy `X w = 1 - e⁻¹ f`, `lc w ∈ Rˣ`, `deg w = n`; so
  `(w, -f)` is good by induction and `(f, w)` is good by the swap.
* `S_i = (X^i g) mod F` satisfies `S_{i+1} = (X S_i) mod F` and `S_{i+1} w ≡ S_i` modulo `f`,
  so `(f, S_{i+1})` good implies `(f, S_i)` good (Mennicke rule + column move).
* `(-c) g ≡ 1 mod F`, so the `R`-linear map `h ↦ ((h g) mod F)(0)` is not into the maximal
  ideal; by locality some `S_j(0)` is a unit (`suslinMonicLocal_exists_isUnit_coeff`), and
  `(f, S_j)` is good by case A.  Descending from `j` to `0` and one column move give `(f, g)`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- Over a local ring, if some `((h g) mod F)(0)` is a unit, so is some `((X^i g) mod F)(0)`. -/
theorem suslinMonicLocal_exists_isUnit_coeff {R : Type*} [CommRing R] [IsLocalRing R]
    (F g h : R[X]) (hu : IsUnit (((h * g) %ₘ F).coeff 0)) :
    ∃ i : ℕ, IsUnit (((X ^ i * g) %ₘ F).coeff 0) := by
  by_contra hne
  push Not at hne
  have key : ∀ h' : R[X], ((h' * g) %ₘ F).coeff 0 ∈ IsLocalRing.maximalIdeal R := by
    intro h'
    induction h' using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [add_mul, add_modByMonic, coeff_add]
      exact Ideal.add_mem _ hp hq
    | monomial i a =>
      rw [← C_mul_X_pow_eq_monomial, mul_assoc, C_mul', smul_modByMonic, coeff_smul,
        smul_eq_mul]
      exact Ideal.mul_mem_left _ a
        ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (hne i)))
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp (key h))) hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_exists_isUnit_coeff

/-- **Case B** of the local monic induction step. -/
theorem suslinMonicLocal_caseB {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ}
    (hIH : ∀ f g : R[X], IsUnit f.leadingCoeff → f.natDegree ≤ n → suslinMonicLocal_Good f g)
    {f g c k : R[X]} (hlc : IsUnit f.leadingCoeff) (hd : f.natDegree = n + 1)
    (he : IsUnit (f.coeff 0)) (hrel : f * k - g * c = 1) : suslinMonicLocal_Good f g := by
  obtain ⟨v, hv⟩ := hlc
  obtain ⟨e, he'⟩ := he
  obtain ⟨F, hF⟩ : ∃ F : R[X], F = C ((v⁻¹ : Rˣ) : R) * f := ⟨_, rfl⟩
  have hFm : F.Monic := by
    rw [hF]
    exact monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [← hv, Units.inv_mul])
  have hFdeg : F.natDegree = f.natDegree := by
    rw [hF]
    exact natDegree_C_mul_of_isUnit (Units.isUnit _) f
  have hF1 : F ≠ 1 := by
    intro h
    rw [h, natDegree_one] at hFdeg
    omega
  have hCv : C (v : R) * C ((v⁻¹ : Rˣ) : R) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hCe : C (e : R) * C ((e⁻¹ : Rˣ) : R) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hfF : f = C (v : R) * F := by
    rw [hF]
    linear_combination (-f) * hCv
  -- the auxiliary polynomial `w` with `X w = 1 - e⁻¹ f`
  obtain ⟨p, hp⟩ := X_dvd_sub_C (p := f)
  rw [← he'] at hp
  have hfpos : 0 < f.natDegree := by omega
  have hXp : (X * p).natDegree = n + 1 := by rw [← hp, natDegree_sub_C, hd]
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [mul_zero, natDegree_zero] at hXp
    omega
  have hpd : p.natDegree = n := by
    rw [natDegree_X_mul hp0] at hXp
    omega
  have hlcp : p.leadingCoeff = f.leadingCoeff := by
    rw [← leadingCoeff_monic_mul (q := p) monic_X, ← hp]
    exact leadingCoeff_sub_of_degree_lt
      (lt_of_le_of_lt degree_C_le (natDegree_pos_iff_degree_pos.mp hfpos))
  obtain ⟨w, hw⟩ : ∃ w : R[X], w = -(C ((e⁻¹ : Rˣ) : R) * p) := ⟨_, rfl⟩
  have hXw : X * w = 1 - C ((e⁻¹ : Rˣ) : R) * f := by
    rw [hw]
    linear_combination C ((e⁻¹ : Rˣ) : R) * hp + hCe
  have hlcw : IsUnit w.leadingCoeff := by
    rw [hw, leadingCoeff_neg, leadingCoeff_C_mul_of_isUnit (Units.isUnit e⁻¹), hlcp, ← hv]
    exact ((Units.isUnit e⁻¹).mul (Units.isUnit v)).neg
  have hwd : w.natDegree = n := by
    rw [hw, natDegree_neg, natDegree_C_mul_of_isUnit (Units.isUnit e⁻¹), hpd]
  have hGw : suslinMonicLocal_Good f w :=
    suslinMonicLocal_good_of_swap (hIH w (-f) hlcw hwd.le) rfl
  -- one descent step: `(f, (X q) mod F)` good implies `(f, q)` good
  have hstep : ∀ q : R[X], suslinMonicLocal_Good f ((X * q) %ₘ F) →
      suslinMonicLocal_Good f q := by
    intro q hq
    have hmd := modByMonic_add_div (X * q) F
    exact suslinMonicLocal_good_of_col_right
      (-(C ((e⁻¹ : Rˣ) : R) * q + C ((v⁻¹ : Rˣ) : R) * ((X * q) /ₘ F) * w))
      (suslinMonicLocal_good_mul_right hq hGw)
      (by linear_combination w * hmd + q * hXw - ((X * q) /ₘ F) * w * hF)
  obtain ⟨Sq, hSq⟩ : ∃ Sq : ℕ → R[X], ∀ i, Sq i = (X ^ i * g) %ₘ F :=
    ⟨fun i ↦ (X ^ i * g) %ₘ F, fun _ ↦ rfl⟩
  have hSsucc : ∀ i, Sq (i + 1) = (X * Sq i) %ₘ F := by
    intro i
    rw [hSq, hSq]
    have hmd := modByMonic_add_div (X ^ i * g) F
    exact modByMonic_eq_of_dvd_sub hFm
      ⟨X * ((X ^ i * g) /ₘ F), by linear_combination (-X) * hmd⟩
  -- a unit constant coefficient somewhere along the orbit
  have h1F : (1 : R[X]) %ₘ F = 1 := (modByMonic_eq_self_iff hFm).mpr (by
    rw [degree_one]
    exact natDegree_pos_iff_degree_pos.mp (by omega))
  have hdvd : F ∣ -c * g - 1 := ⟨-(C (v : R) * k), by linear_combination hrel - k * hfF⟩
  have hu0 : IsUnit (((-c * g) %ₘ F).coeff 0) := by
    rw [modByMonic_eq_of_dvd_sub hFm hdvd, h1F, coeff_one_zero]
    exact isUnit_one
  obtain ⟨j, hj⟩ := suslinMonicLocal_exists_isUnit_coeff F g (-c) hu0
  have hSj : suslinMonicLocal_Good f (Sq j) := by
    rw [hSq]
    exact suslinMonicLocal_caseA hIH ⟨v, hv⟩ hd
      (by rw [← hFdeg]; exact natDegree_modByMonic_lt _ hFm hF1) hj
  have hdown : ∀ m i, suslinMonicLocal_Good f (Sq (i + m)) → suslinMonicLocal_Good f (Sq i) := by
    intro m
    induction m with
    | zero => intro i h; exact h
    | succ m ih =>
      intro i h
      refine hstep (Sq i) ?_
      rw [← hSsucc]
      exact ih (i + 1) (by rw [show i + 1 + m = i + (m + 1) by omega]; exact h)
  have hS0 := hdown j 0 (by rw [zero_add]; exact hSj)
  rw [hSq, pow_zero, one_mul] at hS0
  have hmd := modByMonic_add_div g F
  exact suslinMonicLocal_good_of_col_right (-(C ((v⁻¹ : Rˣ) : R) * (g /ₘ F))) hS0
    (by linear_combination hmd - (g /ₘ F) * hF)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonicLocal_caseB

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
