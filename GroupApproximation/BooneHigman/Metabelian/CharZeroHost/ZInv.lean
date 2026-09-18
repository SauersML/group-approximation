import GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Letters
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.EuclideanDomain.Int
import GroupApproximation.Meta.AxiomGuard

/-!
# The coefficient ring `ℤ[1/m]` (lane bh-met-09)

Research claim: for `m ≠ 0` and a prime `p ∤ m`, the ring `A = ℤ[1/m] = Localization.Away m` is a
Noetherian char-zero domain with digit data `A →+* F_p` whose kernel is `p A`.

**Route.**
* `isDomain_away`, `charZero_away`: `powers m ≤ ℤ⁰` (`powers_le_nonZeroDivisors_of_noZeroDivisors`),
  so the localization is a domain and `ℤ → A` is injective; Noetherianity is a Mathlib instance.
* `redAway`: `IsLocalization.Away.lift`, as `m` is a unit mod `p` (`ZMod.isUnit_iff_coprime`).
* `redAway_exists_eq_mul`: write `z s = a` with `s ∈ powers m` a unit (`IsLocalization.surj`);
  `red z = 0` gives `p ∣ a = p b`, so `z = p (b s⁻¹)`.
* `exists_prime_not_dvd`: a prime `p ≥ m + 2` does not divide `m ≠ 0`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace CharZeroHost

theorem isDomain_away {m : ℕ} (hm : m ≠ 0) : IsDomain (Localization.Away (m : ℤ)) :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (Nat.cast_ne_zero.2 hm))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.isDomain_away

theorem charZero_away {m : ℕ} (hm : m ≠ 0) : CharZero (Localization.Away (m : ℤ)) :=
  charZero_of_injective_algebraMap
    (IsLocalization.injective (Localization.Away (m : ℤ))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (Nat.cast_ne_zero.2 hm)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.charZero_away

theorem isNoetherianRing_away (m : ℕ) : IsNoetherianRing (Localization.Away (m : ℤ)) :=
  inferInstance

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.isNoetherianRing_away

theorem isUnit_castRingHom {m p : ℕ} (hp : p.Prime) (hdvd : ¬p ∣ m) :
    IsUnit (Int.castRingHom (ZMod p) (m : ℤ)) := by
  rw [eq_intCast (Int.castRingHom (ZMod p)) (m : ℤ), Int.cast_natCast]
  exact (ZMod.isUnit_iff_coprime m p).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hdvd).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.isUnit_castRingHom

/-- Reduction `ℤ[1/m] →+* F_p` for a prime `p ∤ m`. -/
noncomputable def redAway {m p : ℕ} (hp : p.Prime) (hdvd : ¬p ∣ m) :
    Localization.Away (m : ℤ) →+* ZMod p :=
  IsLocalization.Away.lift (m : ℤ) (isUnit_castRingHom hp hdvd)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.redAway

theorem redAway_exists_eq_mul {m p : ℕ} (hp : p.Prime) (hdvd : ¬p ∣ m)
    (z : Localization.Away (m : ℤ)) (hz : redAway hp hdvd z = 0) :
    ∃ y : Localization.Away (m : ℤ), z = (p : Localization.Away (m : ℤ)) * y := by
  obtain ⟨x, hs⟩ := IsLocalization.surj (Submonoid.powers (m : ℤ)) z
  have hu : IsUnit (algebraMap ℤ (Localization.Away (m : ℤ)) x.2) :=
    IsLocalization.map_units (Localization.Away (m : ℤ)) x.2
  have ha : ((x.1 : ℤ) : ZMod p) = 0 := by
    have h := congrArg (redAway hp hdvd) hs
    rw [map_mul, hz, zero_mul, eq_intCast (algebraMap ℤ (Localization.Away (m : ℤ))) x.1,
      map_intCast] at h
    exact h.symm
  obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x.1 p).1 ha
  refine ⟨algebraMap ℤ (Localization.Away (m : ℤ)) b * ↑hu.unit⁻¹, ?_⟩
  calc z = z * algebraMap ℤ (Localization.Away (m : ℤ)) x.2 * ↑hu.unit⁻¹ := by
        rw [mul_assoc, hu.mul_val_inv, mul_one]
    _ = (p : Localization.Away (m : ℤ)) *
        (algebraMap ℤ (Localization.Away (m : ℤ)) b * ↑hu.unit⁻¹) := by
        rw [hs, hb, map_mul, map_natCast, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.redAway_exists_eq_mul

/-- Digit data for `ℤ[1/m]` at a prime `p ∤ m`. -/
noncomputable def digitAway {m p : ℕ} (hp : p.Prime) (hdvd : ¬p ∣ m) :
    DigitData (Localization.Away (m : ℤ)) p where
  red := redAway hp hdvd
  exists_eq_mul := redAway_exists_eq_mul hp hdvd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.digitAway

theorem exists_prime_not_dvd {m : ℕ} (hm : m ≠ 0) : ∃ p : ℕ, p.Prime ∧ ¬p ∣ m := by
  obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (m + 2)
  refine ⟨p, hp, fun h => ?_⟩
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.exists_prime_not_dvd

/-- `ℤ[1/0]` is the zero ring. -/
theorem away_zero_eq_one {m : ℕ} (hm : m = 0) : (0 : Localization.Away (m : ℤ)) = 1 := by
  have hmem : (0 : ℤ) ∈ Submonoid.powers (m : ℤ) :=
    (Submonoid.mem_powers_iff 0 (m : ℤ)).2 ⟨1, by rw [pow_one, hm, Nat.cast_zero]⟩
  have h : IsUnit (algebraMap ℤ (Localization.Away (m : ℤ)) 0) :=
    IsLocalization.map_units (Localization.Away (m : ℤ)) (⟨0, hmem⟩ : Submonoid.powers (m : ℤ))
  rwa [map_zero, isUnit_zero_iff] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.away_zero_eq_one

end CharZeroHost
end Metabelian
end BooneHigman
end GroupApproximation
