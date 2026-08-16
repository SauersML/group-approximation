import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# The integers are a Jacobson ring

Section 46.1 reduces "a field finitely generated as a ring is finite" to the
general Nullstellensatz over a Jacobson base, and the base needed there is `ℤ`.
Mathlib has the Nullstellensatz over an arbitrary Jacobson ring but not this
instance, so it is supplied here.

The proof is the classical one: a nonzero prime of `ℤ` is maximal, and the
intersection of all maximal ideals is trivial because an integer divisible by
arbitrarily large primes is zero.
-/

namespace GroupApproximation

/-- The intersection of all maximal ideals of `ℤ` is trivial. -/
theorem int_jacobson_bot : (⊥ : Ideal ℤ).jacobson = ⊥ := by
  refine le_antisymm ?_ Ideal.le_jacobson
  intro n hn
  rw [Ideal.mem_bot]
  by_contra hne
  obtain ⟨p, hpbig, hp⟩ := Nat.exists_infinite_primes (n.natAbs + 1)
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hsurj : Function.Surjective (Int.castRingHom (ZMod p)) :=
    ZMod.intCast_surjective
  have hmax : (RingHom.ker (Int.castRingHom (ZMod p))).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ hsurj
  have hmem : n ∈ RingHom.ker (Int.castRingHom (ZMod p)) :=
    (Ideal.mem_sInf.mp hn) ⟨bot_le, hmax⟩
  rw [RingHom.mem_ker] at hmem
  have hdvd : (p : ℤ) ∣ n := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hmem
  have hnat : p ∣ n.natAbs := by
    have hd := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using hd
  have hne' : n.natAbs ≠ 0 := by
    simpa using hne
  have hple := Nat.le_of_dvd (Nat.pos_of_ne_zero hne') hnat
  omega

instance intIsJacobsonRing : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  rcases eq_or_ne P ⊥ with rfl | hne
  · exact int_jacobson_bot
  · haveI := hP
    haveI : P.IsMaximal := _root_.IsPrime.to_maximal_ideal hne
    exact Ideal.jacobson_eq_self_of_isMaximal

end GroupApproximation
