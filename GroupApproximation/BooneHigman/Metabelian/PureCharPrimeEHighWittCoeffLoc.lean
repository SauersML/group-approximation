import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittCoeffChar
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.CharP.Algebra
import GroupApproximation.Meta.AxiomGuard

/-!
# The coefficient ring `D = ZMod (p²)[σ]_(p)` (bh-met-87e, part 3)

For a prime `p` and a type `σ` of variables we fix:
* `D₀ = MvPolynomial σ (ZMod (p²))`;
* the reduction `red : D₀ → 𝔽_p[σ]` (`eHighWittCoeff_red`);
* the submonoid `S = red⁻¹(nonzerodivisors)` (`eHighWittCoeff_S`), which is the complement of the
  prime `(p)`;
* its localization `D = S⁻¹ D₀` (`eHighWittCoeff_D`), which is the local ring `D₀` localized
  at `(p)`;
* the field `L = Frac(𝔽_p[σ])` (`eHighWittCoeff_L`).

We also prove the kernel of the reduction is `p · D₀` (`eHighWittCoeff_red_eq_zero`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

noncomputable section

variable (p : ℕ) (σ : Type)

/-- Coefficientwise reduction `ZMod (p²)[σ] → 𝔽_p[σ]`. -/
def eHighWittCoeff_red : MvPolynomial σ (ZMod (p ^ 2)) →+* MvPolynomial σ (ZMod p) :=
  MvPolynomial.map (ZMod.castHom (dvd_pow_self p (two_ne_zero : (2 : ℕ) ≠ 0)) (ZMod p))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_red

/-- The elements whose reduction mod `p` is a nonzerodivisor, i.e. is nonzero. -/
def eHighWittCoeff_S : Submonoid (MvPolynomial σ (ZMod (p ^ 2))) :=
  Submonoid.comap (eHighWittCoeff_red p σ) (nonZeroDivisors (MvPolynomial σ (ZMod p)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_S

/-- The coefficient ring `D = ZMod (p²)[σ]` localized at the prime `(p)`. -/
abbrev eHighWittCoeff_D : Type := Localization (eHighWittCoeff_S p σ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_D

/-- The residue field `L = Frac(𝔽_p[σ])`. -/
abbrev eHighWittCoeff_L : Type := FractionRing (MvPolynomial σ (ZMod p))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_L

/-- The kernel of `ZMod (p²) → ZMod p` lies in `(p)`. -/
theorem eHighWittCoeff_zmod_ker [Fact p.Prime] (x : ZMod (p ^ 2))
    (hx : ZMod.castHom (dvd_pow_self p (two_ne_zero : (2 : ℕ) ≠ 0)) (ZMod p) x = 0) :
    x ∈ Ideal.span {((p : ℕ) : ZMod (p ^ 2))} := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, CharP.cast_eq_zero_iff (ZMod p) p] at hx
  obtain ⟨c, hc⟩ := hx
  rw [Ideal.mem_span_singleton']
  exact ⟨(c : ZMod (p ^ 2)), by rw [← ZMod.natCast_zmod_val x, hc, Nat.cast_mul, mul_comm]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_zmod_ker

/-- **The kernel of the reduction is `p · D₀`.** -/
theorem eHighWittCoeff_red_eq_zero [Fact p.Prime] {a : MvPolynomial σ (ZMod (p ^ 2))}
    (h : eHighWittCoeff_red p σ a = 0) :
    ∃ b, a = ((p : ℕ) : MvPolynomial σ (ZMod (p ^ 2))) * b := by
  have hker : a ∈ RingHom.ker (eHighWittCoeff_red p σ) := RingHom.mem_ker.mpr h
  rw [eHighWittCoeff_red, MvPolynomial.ker_map] at hker
  have hle : RingHom.ker (ZMod.castHom (dvd_pow_self p (two_ne_zero : (2 : ℕ) ≠ 0)) (ZMod p)) ≤
      Ideal.span {((p : ℕ) : ZMod (p ^ 2))} :=
    fun x hx => eHighWittCoeff_zmod_ker p x (RingHom.mem_ker.mp hx)
  have h2 := Ideal.map_mono (f := (MvPolynomial.C : ZMod (p ^ 2) →+* MvPolynomial σ _)) hle hker
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton', map_natCast] at h2
  obtain ⟨b, hb⟩ := h2
  exact ⟨b, hb.symm.trans (mul_comm b _)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittCoeff_red_eq_zero

end

end GroupApproximation.BooneHigman.Metabelian.Coprimary
