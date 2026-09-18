import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittCoeffLoc
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import GroupApproximation.Meta.AxiomGuard

/-!
# `D = ZMod (p²)[σ]_(p)`: the prime `p` (bh-met-87f, part 1)

Elementary facts about `p` in `D₀ = ZMod (p²)[σ]` and in its localization
`D = eHighWittCoeff_D p σ` at the prime `(p)`, used to prove that `D` is self-injective
(`PureCharPrimeEHighWittModInjBaer.lean`) and that finite-length `D`-modules embed in `Dˢ`
(`PureCharPrimeEHighWittModInjEmbed.lean`).

* `eHighWittModInj_red_eq_zero_of_p_mul`: if `p · c = 0` in `D₀` then `c ≡ 0 mod p`
  (coefficientwise: `p · x = 0` in `ZMod (p²)` forces `p ∣ x`);
* `eHighWittModInj_red_ne_zero_of_mem`, `eHighWittModInj_mem_of_red_ne_zero`: `S` is exactly
  the set of `a` with `a mod p ≠ 0` (`𝔽_p[σ]` is a domain);
* `eHighWittModInj_p_mul_p`: `p² = 0` in `D`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

variable (p : ℕ) (σ : Type)

/-- In `ZMod (p²)`, `p · x = 0` forces `x ≡ 0 mod p`. -/
theorem eHighWittModInj_zmod_cast_eq_zero [Fact p.Prime] (x : ZMod (p ^ 2))
    (h : ((p : ℕ) : ZMod (p ^ 2)) * x = 0) :
    ZMod.castHom (dvd_pow_self p (two_ne_zero : (2 : ℕ) ≠ 0)) (ZMod p) x = 0 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, ← Nat.cast_mul, CharP.cast_eq_zero_iff (ZMod (p ^ 2)) (p ^ 2)]
    at h
  have h2 : p ∣ x.val := Nat.dvd_of_mul_dvd_mul_left hp.pos (by rw [← pow_two]; exact h)
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, CharP.cast_eq_zero_iff (ZMod p) p]
  exact h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_zmod_cast_eq_zero

/-- In `D₀ = ZMod (p²)[σ]`, `p · c = 0` forces `c ≡ 0 mod p`. -/
theorem eHighWittModInj_red_eq_zero_of_p_mul [Fact p.Prime] {c : MvPolynomial σ (ZMod (p ^ 2))}
    (h : ((p : ℕ) : MvPolynomial σ (ZMod (p ^ 2))) * c = 0) :
    eHighWittCoeff_red p σ c = 0 := by
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [eHighWittCoeff_red, MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
  have hm := congrArg (MvPolynomial.coeff m) h
  have hC : ((p : ℕ) : MvPolynomial σ (ZMod (p ^ 2))) =
      MvPolynomial.C ((p : ℕ) : ZMod (p ^ 2)) :=
    (map_natCast (MvPolynomial.C : ZMod (p ^ 2) →+* MvPolynomial σ (ZMod (p ^ 2))) p).symm
  rw [hC, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_zero] at hm
  exact eHighWittModInj_zmod_cast_eq_zero p (MvPolynomial.coeff m c) hm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_red_eq_zero_of_p_mul

/-- Elements of `S` reduce to nonzero polynomials mod `p`. -/
theorem eHighWittModInj_red_ne_zero_of_mem {s : MvPolynomial σ (ZMod (p ^ 2))}
    (hs : s ∈ eHighWittCoeff_S p σ) : eHighWittCoeff_red p σ s ≠ 0 :=
  nonZeroDivisors.ne_zero (Submonoid.mem_comap.mp hs)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_red_ne_zero_of_mem

/-- An element with nonzero reduction mod `p` lies in `S`. -/
theorem eHighWittModInj_mem_of_red_ne_zero {a : MvPolynomial σ (ZMod (p ^ 2))}
    (ha : eHighWittCoeff_red p σ a ≠ 0) : a ∈ eHighWittCoeff_S p σ :=
  Submonoid.mem_comap.mpr (mem_nonZeroDivisors_of_ne_zero ha)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_mem_of_red_ne_zero

/-- `p² = 0` in `D₀`. -/
theorem eHighWittModInj_p_mul_p_R0 :
    ((p : ℕ) : MvPolynomial σ (ZMod (p ^ 2))) * ((p : ℕ) : MvPolynomial σ (ZMod (p ^ 2))) = 0 := by
  rw [← Nat.cast_mul, ← pow_two,
    ← map_natCast (MvPolynomial.C : ZMod (p ^ 2) →+* MvPolynomial σ (ZMod (p ^ 2))) (p ^ 2),
    ZMod.natCast_self, map_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_p_mul_p_R0

/-- **`p² = 0` in `D`.** -/
theorem eHighWittModInj_p_mul_p :
    ((p : ℕ) : eHighWittCoeff_D p σ) * ((p : ℕ) : eHighWittCoeff_D p σ) = 0 := by
  rw [← map_natCast (algebraMap (MvPolynomial σ (ZMod (p ^ 2))) (eHighWittCoeff_D p σ)) p,
    ← map_mul, eHighWittModInj_p_mul_p_R0, map_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_p_mul_p

/-- `p² = 0` in `D`, as a power. -/
theorem eHighWittModInj_p_sq : ((p : ℕ) : eHighWittCoeff_D p σ) ^ 2 = 0 := by
  rw [pow_two]
  exact eHighWittModInj_p_mul_p p σ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_p_sq

end GroupApproximation.BooneHigman.Metabelian.Coprimary
