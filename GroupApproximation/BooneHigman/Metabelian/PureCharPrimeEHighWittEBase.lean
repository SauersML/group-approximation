import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittEChain
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import GroupApproximation.Meta.AxiomGuard

/-!
# The chain ring `D_e = ZMod (p^e)[σ]_(p)` (bh-met-87h, part 2)

For a prime `p`, a length `e ≠ 0` and a type `σ` of variables we fix:

* `D₀ = MvPolynomial σ (ZMod (p ^ e))`;
* the reduction `red : D₀ → 𝔽_p[σ]` (`eHighWittE_red`);
* `S = red⁻¹(nonzerodivisors)` (`eHighWittE_S`), the complement of the prime `(p)`;
* the localization `D_e = S⁻¹ D₀` (`eHighWittE_D`).

Then `D_e` is a chain ring of length `e` with uniformizer `p` (`eHighWittE_isChain`):

* the kernel of `red` is `p D₀`, so every element of `D_e` is a unit or in `p D_e`;
* `p ^ e = 0`;
* `p ^ j ≠ 0` for `j < e`, since `p ^ j · x = 0` in `ZMod (p ^ e)` forces `p ∣ x`.

This generalises `PureCharPrimeEHighWittCoeffLoc.lean` and `…ModInjBase/Local.lean` (`e = 2`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

noncomputable section

variable (p e : ℕ) [NeZero e] (σ : Type)

/-- Coefficientwise reduction `ZMod (p ^ e)[σ] → 𝔽_p[σ]`. -/
def eHighWittE_red : MvPolynomial σ (ZMod (p ^ e)) →+* MvPolynomial σ (ZMod p) :=
  MvPolynomial.map (ZMod.castHom (dvd_pow_self p (NeZero.ne e)) (ZMod p))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_red

/-- The elements whose reduction mod `p` is a nonzerodivisor, i.e. is nonzero. -/
def eHighWittE_S : Submonoid (MvPolynomial σ (ZMod (p ^ e))) :=
  Submonoid.comap (eHighWittE_red p e σ) (nonZeroDivisors (MvPolynomial σ (ZMod p)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_S

/-- The chain ring `D_e = ZMod (p ^ e)[σ]` localized at the prime `(p)`. -/
abbrev eHighWittE_D : Type := Localization (eHighWittE_S p e σ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_D

/-- The kernel of `ZMod (p ^ e) → ZMod p` lies in `(p)`. -/
theorem eHighWittE_zmod_ker [Fact p.Prime] (x : ZMod (p ^ e))
    (hx : ZMod.castHom (dvd_pow_self p (NeZero.ne e)) (ZMod p) x = 0) :
    x ∈ Ideal.span {((p : ℕ) : ZMod (p ^ e))} := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, CharP.cast_eq_zero_iff (ZMod p) p] at hx
  obtain ⟨c, hc⟩ := hx
  rw [Ideal.mem_span_singleton']
  exact ⟨(c : ZMod (p ^ e)), by rw [← ZMod.natCast_zmod_val x, hc, Nat.cast_mul, mul_comm]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_zmod_ker

/-- **The kernel of the reduction is `p · D₀`.** -/
theorem eHighWittE_red_eq_zero [Fact p.Prime] {a : MvPolynomial σ (ZMod (p ^ e))}
    (h : eHighWittE_red p e σ a = 0) :
    ∃ b, a = ((p : ℕ) : MvPolynomial σ (ZMod (p ^ e))) * b := by
  have hker : a ∈ RingHom.ker (eHighWittE_red p e σ) := RingHom.mem_ker.mpr h
  rw [eHighWittE_red, MvPolynomial.ker_map] at hker
  have hle : RingHom.ker (ZMod.castHom (dvd_pow_self p (NeZero.ne e)) (ZMod p)) ≤
      Ideal.span {((p : ℕ) : ZMod (p ^ e))} :=
    fun x hx => eHighWittE_zmod_ker p e x (RingHom.mem_ker.mp hx)
  have h2 := Ideal.map_mono (f := (MvPolynomial.C : ZMod (p ^ e) →+* MvPolynomial σ _)) hle hker
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton', map_natCast] at h2
  obtain ⟨b, hb⟩ := h2
  exact ⟨b, hb.symm.trans (mul_comm b _)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_red_eq_zero

/-- In `ZMod (p ^ e)`, `p ^ j · x = 0` with `j < e` forces `x ≡ 0 mod p`. -/
theorem eHighWittE_zmod_cast_eq_zero [Fact p.Prime] {j : ℕ} (hj : j < e) (x : ZMod (p ^ e))
    (h : ((p : ℕ) : ZMod (p ^ e)) ^ j * x = 0) :
    ZMod.castHom (dvd_pow_self p (NeZero.ne e)) (ZMod p) x = 0 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, ← Nat.cast_pow, ← Nat.cast_mul,
    CharP.cast_eq_zero_iff (ZMod (p ^ e)) (p ^ e)] at h
  have h1 : p ^ j * p ∣ p ^ j * x.val := by
    rw [← pow_succ]
    exact (pow_dvd_pow p (by omega : j + 1 ≤ e)).trans h
  have h2 : p ∣ x.val := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos j) h1
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, CharP.cast_eq_zero_iff (ZMod p) p]
  exact h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_zmod_cast_eq_zero

/-- In `D₀`, `p ^ j · c = 0` with `j < e` forces `c ≡ 0 mod p`. -/
theorem eHighWittE_red_eq_zero_of_pow_mul [Fact p.Prime] {j : ℕ} (hj : j < e)
    {c : MvPolynomial σ (ZMod (p ^ e))}
    (h : ((p : ℕ) : MvPolynomial σ (ZMod (p ^ e))) ^ j * c = 0) :
    eHighWittE_red p e σ c = 0 := by
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [eHighWittE_red, MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
  have hm := congrArg (MvPolynomial.coeff m) h
  have hC : ((p : ℕ) : MvPolynomial σ (ZMod (p ^ e))) ^ j =
      MvPolynomial.C (((p : ℕ) : ZMod (p ^ e)) ^ j) := by
    rw [map_pow, map_natCast]
  rw [hC, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_zero] at hm
  exact eHighWittE_zmod_cast_eq_zero p e hj (MvPolynomial.coeff m c) hm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_red_eq_zero_of_pow_mul

/-- Elements of `S` reduce to nonzero polynomials mod `p`. -/
theorem eHighWittE_red_ne_zero_of_mem [Fact p.Prime] {s : MvPolynomial σ (ZMod (p ^ e))}
    (hs : s ∈ eHighWittE_S p e σ) : eHighWittE_red p e σ s ≠ 0 :=
  nonZeroDivisors.ne_zero (Submonoid.mem_comap.mp hs)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_red_ne_zero_of_mem

/-- An element with nonzero reduction mod `p` lies in `S`. -/
theorem eHighWittE_mem_of_red_ne_zero [Fact p.Prime] {a : MvPolynomial σ (ZMod (p ^ e))}
    (ha : eHighWittE_red p e σ a ≠ 0) : a ∈ eHighWittE_S p e σ :=
  Submonoid.mem_comap.mpr (mem_nonZeroDivisors_of_ne_zero ha)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_mem_of_red_ne_zero

/-- If `z · s = a` in `D_e` with `a ≡ 0 mod p`, then `z ∈ p D_e`. -/
theorem eHighWittE_eq_p_mul_of_red [Fact p.Prime] {z : eHighWittE_D p e σ}
    {a : MvPolynomial σ (ZMod (p ^ e))} {s : eHighWittE_S p e σ}
    (h : z * algebraMap (MvPolynomial σ (ZMod (p ^ e))) (eHighWittE_D p e σ) s =
      algebraMap (MvPolynomial σ (ZMod (p ^ e))) (eHighWittE_D p e σ) a)
    (ha : eHighWittE_red p e σ a = 0) :
    ∃ w : eHighWittE_D p e σ, z = ((p : ℕ) : eHighWittE_D p e σ) * w := by
  obtain ⟨b, rfl⟩ := eHighWittE_red_eq_zero p e σ ha
  obtain ⟨u, hu⟩ := IsLocalization.map_units (eHighWittE_D p e σ) s
  refine ⟨algebraMap (MvPolynomial σ (ZMod (p ^ e))) (eHighWittE_D p e σ) b * ↑u⁻¹, ?_⟩
  rw [← mul_assoc, Units.eq_mul_inv_iff_mul_eq, hu, h, map_mul, map_natCast]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_eq_p_mul_of_red

/-- **Every element of `D_e` is a unit or lies in `p D_e`.** -/
theorem eHighWittE_isUnit_or [Fact p.Prime] (z : eHighWittE_D p e σ) :
    IsUnit z ∨ ∃ w : eHighWittE_D p e σ, z = ((p : ℕ) : eHighWittE_D p e σ) * w := by
  obtain ⟨x, hx⟩ := IsLocalization.surj (eHighWittE_S p e σ) z
  by_cases ha : eHighWittE_red p e σ x.1 = 0
  · exact Or.inr (eHighWittE_eq_p_mul_of_red p e σ hx ha)
  · left
    refine isUnit_of_mul_isUnit_left
      (y := algebraMap (MvPolynomial σ (ZMod (p ^ e))) (eHighWittE_D p e σ) x.2) ?_
    rw [hx]
    exact IsLocalization.map_units (eHighWittE_D p e σ)
      ⟨x.1, eHighWittE_mem_of_red_ne_zero p e σ ha⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_isUnit_or

/-- `p ^ e = 0` in `D_e`. -/
theorem eHighWittE_p_pow_eq_zero : ((p : ℕ) : eHighWittE_D p e σ) ^ e = 0 := by
  rw [← map_natCast (algebraMap (MvPolynomial σ (ZMod (p ^ e))) (eHighWittE_D p e σ)) p,
    ← map_pow, ← Nat.cast_pow,
    ← map_natCast (MvPolynomial.C : ZMod (p ^ e) →+* MvPolynomial σ (ZMod (p ^ e))) (p ^ e),
    ZMod.natCast_self, map_zero, map_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_p_pow_eq_zero

/-- `p ^ j ≠ 0` in `D_e` for `j < e`. -/
theorem eHighWittE_p_pow_ne_zero [Fact p.Prime] {j : ℕ} (hj : j < e) :
    ((p : ℕ) : eHighWittE_D p e σ) ^ j ≠ 0 := by
  intro h
  rw [← map_natCast (algebraMap (MvPolynomial σ (ZMod (p ^ e))) (eHighWittE_D p e σ)) p,
    ← map_pow, IsLocalization.map_eq_zero_iff (eHighWittE_S p e σ) (eHighWittE_D p e σ)] at h
  obtain ⟨t, ht⟩ := h
  exact eHighWittE_red_ne_zero_of_mem p e σ t.2
    (eHighWittE_red_eq_zero_of_pow_mul p e σ hj ((mul_comm _ _).trans ht))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_p_pow_ne_zero

/-- **`D_e` is a chain ring of length `e` with uniformizer `p`.** -/
theorem eHighWittE_isChain [Fact p.Prime] :
    eHighWittE_IsChain ((p : ℕ) : eHighWittE_D p e σ) e :=
  ⟨eHighWittE_isUnit_or p e σ, eHighWittE_p_pow_eq_zero p e σ,
    fun _ hj => eHighWittE_p_pow_ne_zero p e σ hj⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_isChain

end

end GroupApproximation.BooneHigman.Metabelian.Coprimary
