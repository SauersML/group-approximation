import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittCoeffLoc
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Maximal
import GroupApproximation.Meta.AxiomGuard

/-!
# `D` is an Artinian ring (bh-met-87g, part 3)

`D = ZMod (p²)[X₁..X_d]_(p)` (`eHighWittCoeff_D`) is Noetherian, being a localization of a
Noetherian ring. Its Krull dimension is `0`. Let `I` be a prime of `D`.
* `p · p = 0` in `D`, so `p ∈ I`.
* If `x ∉ I`, write `x · s = a` with `s ∈ S`. If `red a = 0`, then `a = p b ∈ I`, so `x ∈ I` or
  `s ∈ I`, and both are impossible (`s` is a unit). Hence `a ∈ S`, `x · s` is a unit, and so
  `x` is a unit.
So every prime is maximal, and Hopkins–Levitzki gives that `D` is Artinian. We use this to feed
the finite-length hypothesis of `EHighWittModEmbedStatement`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- **`D` is Artinian.** -/
theorem eHighWittModRed_isArtinianRing (p : ℕ) [Fact p.Prime] (d : ℕ) :
    IsArtinianRing (eHighWittCoeff_D p (Fin d)) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  haveI : IsNoetherianRing (ZMod (p ^ 2)) :=
    _root_.isNoetherian_of_finite (ZMod (p ^ 2)) (ZMod (p ^ 2))
  haveI : Ring.KrullDimLE 0 (eHighWittCoeff_D p (Fin d)) := by
    refine Ring.KrullDimLE.mk₀ fun I hI => ?_
    have hpp : ((p * p : ℕ) : MvPolynomial (Fin d) (ZMod (p ^ 2))) = 0 :=
      (CharP.cast_eq_zero_iff (MvPolynomial (Fin d) (ZMod (p ^ 2))) (p ^ 2) (p * p)).mpr
        ⟨1, by ring⟩
    have hpD : ((p : ℕ) : eHighWittCoeff_D p (Fin d)) * ((p : ℕ) : eHighWittCoeff_D p (Fin d)) =
        0 := by
      rw [← Nat.cast_mul, ← map_natCast (algebraMap (MvPolynomial (Fin d) (ZMod (p ^ 2)))
        (eHighWittCoeff_D p (Fin d))), hpp, map_zero]
    have hpI : ((p : ℕ) : eHighWittCoeff_D p (Fin d)) ∈ I := by
      have h0 : ((p : ℕ) : eHighWittCoeff_D p (Fin d)) * ((p : ℕ) : eHighWittCoeff_D p (Fin d)) ∈
          I := by
        rw [hpD]
        exact I.zero_mem
      rcases hI.mem_or_mem h0 with h | h <;> exact h
    have hunit : ∀ x : eHighWittCoeff_D p (Fin d), x ∉ I → IsUnit x := by
      intro x hx
      obtain ⟨y, hs⟩ := IsLocalization.surj (eHighWittCoeff_S p (Fin d)) x
      have hsu : IsUnit (algebraMap (MvPolynomial (Fin d) (ZMod (p ^ 2)))
          (eHighWittCoeff_D p (Fin d)) (y.2 : MvPolynomial (Fin d) (ZMod (p ^ 2)))) :=
        IsLocalization.map_units (eHighWittCoeff_D p (Fin d)) y.2
      by_cases ha : eHighWittCoeff_red p (Fin d) y.1 = 0
      · exfalso
        obtain ⟨b, hb⟩ := eHighWittCoeff_red_eq_zero p (Fin d) ha
        have hmem : x * algebraMap (MvPolynomial (Fin d) (ZMod (p ^ 2)))
            (eHighWittCoeff_D p (Fin d)) (y.2 : MvPolynomial (Fin d) (ZMod (p ^ 2))) ∈ I := by
          rw [hs, hb, map_mul, map_natCast]
          exact I.mul_mem_right _ hpI
        rcases hI.mem_or_mem hmem with h | h
        · exact hx h
        · exact hI.ne_top (Ideal.eq_top_of_isUnit_mem I h hsu)
      · have haS : y.1 ∈ eHighWittCoeff_S p (Fin d) :=
          Submonoid.mem_comap.mpr (mem_nonZeroDivisors_of_ne_zero ha)
        have hxu : IsUnit (x * algebraMap (MvPolynomial (Fin d) (ZMod (p ^ 2)))
            (eHighWittCoeff_D p (Fin d)) (y.2 : MvPolynomial (Fin d) (ZMod (p ^ 2)))) := by
          rw [hs]
          exact IsLocalization.map_units (eHighWittCoeff_D p (Fin d)) ⟨y.1, haS⟩
        exact isUnit_of_mul_isUnit_left hxu
    refine Ideal.isMaximal_iff.mpr ⟨(Ideal.ne_top_iff_one I).mp hI.ne_top, ?_⟩
    intro J x _ hxI hxJ
    exact (Ideal.eq_top_iff_one J).mp (Ideal.eq_top_of_isUnit_mem J hxJ (hunit x hxI))
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModRed_isArtinianRing

end GroupApproximation.BooneHigman.Metabelian.Coprimary
