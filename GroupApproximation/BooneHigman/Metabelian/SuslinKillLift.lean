import GroupApproximation.BooneHigman.Metabelian.SuslinKillElim
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Localization.Ideal
import GroupApproximation.Meta.AxiomGuard

/-!
# Killing primes, part 2: the leading-coefficient ideal lies in no principal prime

Lane `bh-met-91t`.  `C` a UFD, `J ⊆ C[X]` in no principal prime.  Then the ideal `lc(J)` of
leading coefficients lies in no principal prime `(p)` of `C`.

Proof: `C c ∈ J` with `c ≠ 0` (`SuslinKillElim`); write `c = p^n u`, `p ∤ u`.  `J ⊄ (C p)`
(`C p` is prime), so some `g ∈ J` has `C p ∤ g`; truncating the coefficients divisible by `p`
from the top gives `h` with `g - h = C p w` and `p ∤ lc h`.  Then
`C u h^n = C u (h^n - (-C p w)^n) + (-1)^n w^n C c ∈ J` (as `g ∣ h^n - (-C p w)^n`), and its
leading coefficient `u lc(h)^n` is prime to `p`.

Also: transport of "no principal prime" along a ring isomorphism, the PID base fact, and the
principal-ideal-ring instance for `ℤ[1/m]`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- Truncation: if `C p ∤ g`, then `g ≡ h (mod C p)` with `p ∤ lc h`. -/
theorem suslinKill_trunc {C : Type*} [CommRing C] (p : C) :
    ∀ (d : ℕ) (g : C[X]), g.natDegree = d → ¬Polynomial.C p ∣ g →
      ∃ h : C[X], Polynomial.C p ∣ g - h ∧ ¬p ∣ h.leadingCoeff := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro g hd hg
    by_cases hl : p ∣ g.leadingCoeff
    · have hsplit := g.eraseLead_add_C_mul_X_pow
      obtain ⟨a, ha⟩ := hl
      have hdvd : Polynomial.C p ∣ Polynomial.C g.leadingCoeff * (X : C[X]) ^ g.natDegree :=
        ⟨Polynomial.C a * (X : C[X]) ^ g.natDegree, by rw [ha, map_mul]; ring⟩
      have he : ¬Polynomial.C p ∣ g.eraseLead := by
        intro h'
        apply hg
        rw [← hsplit]
        exact dvd_add h' hdvd
      have hlt : g.eraseLead.natDegree < d := by
        rcases g.eraseLead_natDegree_lt_or_eraseLead_eq_zero with h' | h'
        · omega
        · exact absurd (by rw [h']; exact dvd_zero _) he
      obtain ⟨h, hh1, hh2⟩ := ih _ hlt _ rfl he
      refine ⟨h, ?_, hh2⟩
      have heq : g - h = (g.eraseLead - h) +
          Polynomial.C g.leadingCoeff * (X : C[X]) ^ g.natDegree := by
        conv_lhs => rw [← hsplit]
        ring
      rw [heq]
      exact dvd_add hh1 hdvd
    · exact ⟨g, by simp, hl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_trunc

/-- **Key lemma**: over a UFD `C`, if `J ⊆ C[X]` lies in no principal prime, then so does
its leading-coefficient ideal `J.leadingCoeff ⊆ C`. -/
theorem suslinKill_lc_avoid {C : Type*} [CommRing C] [IsDomain C]
    [UniqueFactorizationMonoid C] (J : Ideal C[X])
    (hJ : ∀ π : C[X], Prime π → ¬J ≤ Ideal.span {π}) :
    ∀ p : C, Prime p → ¬J.leadingCoeff ≤ Ideal.span {p} := by
  intro p hp hle
  obtain ⟨c, hc0, hcJ⟩ := suslinKill_exists_C_mem J hJ
  obtain ⟨g, hgJ, hg⟩ :=
    SetLike.not_le_iff_exists.1 (hJ _ (Polynomial.prime_C_iff.2 hp))
  rw [Ideal.mem_span_singleton] at hg
  obtain ⟨h, ⟨w, hw⟩, hh⟩ := suslinKill_trunc p _ g rfl hg
  obtain ⟨n, u, hu, hcu⟩ := WfDvdMonoid.max_power_factor' hc0 hp.not_unit
  have hmem : Polynomial.C u * h ^ n ∈ J := by
    obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow h (-(Polynomial.C p * w)) n
    have hg' : h - -(Polynomial.C p * w) = g := by
      rw [← hw]
      ring
    rw [hg'] at ht
    have key : Polynomial.C u * h ^ n =
        Polynomial.C u * (g * t) + (-1) ^ n * w ^ n * Polynomial.C c := by
      rw [← ht, neg_pow (Polynomial.C p * w), mul_pow (Polynomial.C p) w n, hcu, map_mul,
        map_pow]
      ring
    rw [key]
    exact J.add_mem (J.mul_mem_left _ (J.mul_mem_right _ hgJ)) (J.mul_mem_left _ hcJ)
  have hlc : u * h.leadingCoeff ^ n ∈ Ideal.span {p} := by
    refine hle ?_
    rw [Ideal.mem_leadingCoeff]
    refine ⟨_, hmem, ?_⟩
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_pow]
  rw [Ideal.mem_span_singleton] at hlc
  rcases hp.dvd_or_dvd hlc with h1 | h1
  · exact hu h1
  · exact hh (hp.dvd_of_dvd_pow h1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_lc_avoid

/-- Transport along a ring isomorphism `e : B ≃+* B'`: if `J` lies in no principal prime,
neither does `e(J) = (e⁻¹)⁻¹(J)`. -/
theorem suslinKill_comap_avoid {B B' : Type*} [CommRing B] [CommRing B'] (e : B ≃+* B')
    {J : Ideal B} (hJ : ∀ π : B, Prime π → ¬J ≤ Ideal.span {π}) :
    ∀ π : B', Prime π → ¬J.comap e.symm ≤ Ideal.span {π} := by
  intro π hπ hle
  have hπ' : Prime (e.symm π) := (MulEquiv.prime_iff e.symm).2 hπ
  refine hJ (e.symm π) hπ' fun x hx ↦ ?_
  have hex : e x ∈ J.comap e.symm := by
    rw [Ideal.mem_comap, RingEquiv.symm_apply_apply]
    exact hx
  have hd : π ∣ e x := Ideal.mem_span_singleton.1 (hle hex)
  have hd' := map_dvd e.symm hd
  rw [RingEquiv.symm_apply_apply] at hd'
  exact Ideal.mem_span_singleton.2 hd'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_comap_avoid

/-- PID base fact: a nonzero ideal of a PID domain lying in no principal prime contains `1`. -/
theorem suslinKill_one_mem {C : Type*} [CommRing C] [IsDomain C] [IsPrincipalIdealRing C]
    (I : Ideal C) (h0 : I ≠ ⊥) (hI : ∀ p : C, Prime p → ¬I ≤ Ideal.span {p}) :
    (1 : C) ∈ I := by
  obtain ⟨a, rfl⟩ : ∃ a : C, I = Ideal.span {a} :=
    ⟨_, (Ideal.span_singleton_generator I).symm⟩
  have ha : a ≠ 0 := by
    rintro rfl
    exact h0 (Ideal.span_singleton_eq_bot.2 rfl)
  by_cases hu : IsUnit a
  · exact Ideal.mem_span_singleton.2 hu.dvd
  · obtain ⟨p, hp, hpa⟩ := WfDvdMonoid.exists_irreducible_factor hu ha
    exact absurd (Ideal.span_singleton_le_span_singleton.2 hpa)
      (hI p (UniqueFactorizationMonoid.irreducible_iff_prime.1 hp))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_one_mem

/-- `ℤ[1/m]` is a principal ideal ring (every ideal is extended from `ℤ`). -/
theorem suslinKill_away_pid (m : ℕ) : IsPrincipalIdealRing (Localization.Away (m : ℤ)) := by
  refine ⟨fun J ↦ ?_⟩
  rw [← IsLocalization.map_under (Submonoid.powers (m : ℤ)) (Localization.Away (m : ℤ)) J,
    ← Ideal.span_singleton_generator (J.under ℤ), Ideal.map_span, Set.image_singleton]
  exact ⟨⟨_, rfl⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_away_pid

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
