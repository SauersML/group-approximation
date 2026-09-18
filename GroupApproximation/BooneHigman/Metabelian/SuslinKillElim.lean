import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Killing primes, part 1: a nonzero constant in an ideal lying in no principal prime

Lane `bh-met-91t`.  Over a UFD `C`, an ideal `J ⊆ C[X]` lying in no principal prime contains
a nonzero constant `C c`.

Proof: take `g ∈ J`, `g ≠ 0`, of minimal `X`-degree.  If `deg g = 0` it is a constant.
Otherwise `g` has a prime factor `π` of positive degree.  For every `h ∈ J`, pseudo-division
gives `lc(g)^N h - q g` in `J` of degree `< deg g`, so it is `0`.  Hence `π ∣ C(lc g)^N h`, and
`π` cannot divide the nonzero constant `C(lc g)^N`, so `π ∣ h`: `J ⊆ (π)`, a contradiction.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- Pseudo-division over a domain, in `natDegree` form (`deg g > 0`). -/
theorem suslinKill_pseudoDiv {C : Type*} [CommRing C] [IsDomain C] (g : C[X]) (hg : g ≠ 0)
    (hpos : 0 < g.natDegree) :
    ∀ (d : ℕ) (h : C[X]), h.natDegree ≤ d →
      ∃ (N : ℕ) (q : C[X]), (Polynomial.C g.leadingCoeff ^ N * h - q * g).natDegree <
        g.natDegree := by
  intro d
  induction d with
  | zero =>
    intro h hh
    exact ⟨0, 0, by simpa using lt_of_le_of_lt hh hpos⟩
  | succ d ih =>
    intro h hh
    by_cases hlt : h.natDegree < g.natDegree
    · exact ⟨0, 0, by simpa using hlt⟩
    push Not at hlt
    obtain ⟨k, hk⟩ : ∃ k, h.natDegree = k + g.natDegree := ⟨h.natDegree - g.natDegree, by omega⟩
    have hh0 : h ≠ 0 := by
      rintro rfl
      rw [Polynomial.natDegree_zero] at hlt
      omega
    have hlg : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hg
    have hlh : h.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hh0
    have hm0 : Polynomial.C h.leadingCoeff * (X : C[X]) ^ k ≠ 0 :=
      mul_ne_zero (Polynomial.C_ne_zero.2 hlh) (pow_ne_zero _ Polynomial.X_ne_zero)
    have hp0 : Polynomial.C g.leadingCoeff * h ≠ 0 :=
      mul_ne_zero (Polynomial.C_ne_zero.2 hlg) hh0
    have hq0 : Polynomial.C h.leadingCoeff * (X : C[X]) ^ k * g ≠ 0 := mul_ne_zero hm0 hg
    have hpd : (Polynomial.C g.leadingCoeff * h).natDegree = h.natDegree :=
      Polynomial.natDegree_C_mul hlg
    have hqd : (Polynomial.C h.leadingCoeff * (X : C[X]) ^ k * g).natDegree = h.natDegree := by
      rw [Polynomial.natDegree_mul hm0 hg, Polynomial.natDegree_C_mul_X_pow k _ hlh]
      omega
    have hdeg : (Polynomial.C g.leadingCoeff * h).degree =
        (Polynomial.C h.leadingCoeff * (X : C[X]) ^ k * g).degree := by
      rw [Polynomial.degree_eq_natDegree hp0, Polynomial.degree_eq_natDegree hq0, hpd, hqd]
    have hlc : (Polynomial.C g.leadingCoeff * h).leadingCoeff =
        (Polynomial.C h.leadingCoeff * (X : C[X]) ^ k * g).leadingCoeff := by
      simp only [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
        Polynomial.leadingCoeff_X_pow, mul_one]
      exact mul_comm _ _
    have hsub := Polynomial.degree_sub_lt hdeg hp0 hlc
    have hlt1 : (Polynomial.C g.leadingCoeff * h -
        Polynomial.C h.leadingCoeff * (X : C[X]) ^ k * g).natDegree < h.natDegree := by
      by_cases hz : Polynomial.C g.leadingCoeff * h -
          Polynomial.C h.leadingCoeff * (X : C[X]) ^ k * g = 0
      · rw [hz, Polynomial.natDegree_zero]
        omega
      · rw [← hpd]
        exact Polynomial.natDegree_lt_natDegree hz hsub
    obtain ⟨N, q, hq⟩ := ih (Polynomial.C g.leadingCoeff * h -
      Polynomial.C h.leadingCoeff * (X : C[X]) ^ k * g) (by omega)
    refine ⟨N + 1, Polynomial.C g.leadingCoeff ^ N *
      (Polynomial.C h.leadingCoeff * (X : C[X]) ^ k) + q, ?_⟩
    have heq : Polynomial.C g.leadingCoeff ^ (N + 1) * h -
        (Polynomial.C g.leadingCoeff ^ N * (Polynomial.C h.leadingCoeff * (X : C[X]) ^ k) + q) *
          g =
        Polynomial.C g.leadingCoeff ^ N * (Polynomial.C g.leadingCoeff * h -
          Polynomial.C h.leadingCoeff * (X : C[X]) ^ k * g) - q * g := by
      ring
    rw [heq]
    exact hq

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_pseudoDiv

/-- In a UFD `C[X]`, a polynomial of positive degree has a prime factor of positive degree. -/
theorem suslinKill_prime_factor_pos {C : Type*} [CommRing C] [IsDomain C]
    [UniqueFactorizationMonoid C[X]] (g : C[X]) :
    0 < g.natDegree → ∃ π : C[X], Prime π ∧ π ∣ g ∧ 0 < π.natDegree := by
  refine UniqueFactorizationMonoid.induction_on_prime g ?_ ?_ ?_
  · intro h
    simp at h
  · intro x hx h
    rw [Polynomial.natDegree_eq_zero_of_isUnit hx] at h
    omega
  · intro a p ha hp ih h
    by_cases hpd : 0 < p.natDegree
    · exact ⟨p, hp, dvd_mul_right p a, hpd⟩
    · rw [Polynomial.natDegree_mul hp.ne_zero ha] at h
      obtain ⟨π, h1, h2, h3⟩ := ih (by omega)
      exact ⟨π, h1, dvd_mul_of_dvd_right h2 p, h3⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_prime_factor_pos

/-- **Elimination**: an ideal of `C[X]` (`C` a UFD) lying in no principal prime contains a
nonzero constant. -/
theorem suslinKill_exists_C_mem {C : Type*} [CommRing C] [IsDomain C]
    [UniqueFactorizationMonoid C] (J : Ideal C[X])
    (hJ : ∀ π : C[X], Prime π → ¬J ≤ Ideal.span {π}) :
    ∃ c : C, c ≠ 0 ∧ Polynomial.C c ∈ J := by
  classical
  have hex : ∃ d, ∃ g ∈ J, g ≠ 0 ∧ g.natDegree = d := by
    obtain ⟨g, hgJ, hg⟩ := SetLike.not_le_iff_exists.1 (hJ _ Polynomial.prime_X)
    refine ⟨_, g, hgJ, ?_, rfl⟩
    rintro rfl
    exact hg (Ideal.zero_mem _)
  obtain ⟨g, hgJ, hg0, hgd⟩ := Nat.find_spec hex
  have hmin : ∀ r ∈ J, r.natDegree < g.natDegree → r = 0 := by
    intro r hr hlt
    by_contra hr0
    exact Nat.find_min hex (lt_of_lt_of_eq hlt hgd) ⟨r, hr, hr0, rfl⟩
  by_cases hd : g.natDegree = 0
  · refine ⟨g.coeff 0, ?_, ?_⟩
    · intro h0
      apply hg0
      rw [Polynomial.eq_C_of_natDegree_eq_zero hd, h0, map_zero]
    · rw [← Polynomial.eq_C_of_natDegree_eq_zero hd]
      exact hgJ
  exfalso
  obtain ⟨π, hπ, hπg, hπd⟩ := suslinKill_prime_factor_pos g (by omega)
  refine hJ π hπ fun h hh ↦ ?_
  obtain ⟨N, q, hr⟩ := suslinKill_pseudoDiv g hg0 (by omega) _ h le_rfl
  have hrJ : Polynomial.C g.leadingCoeff ^ N * h - q * g ∈ J :=
    J.sub_mem (J.mul_mem_left _ hh) (J.mul_mem_left _ hgJ)
  have hr0 := hmin _ hrJ hr
  rw [sub_eq_zero] at hr0
  have hdiv : π ∣ Polynomial.C g.leadingCoeff ^ N * h := by
    rw [hr0]
    exact dvd_mul_of_dvd_right hπg _
  rw [Ideal.mem_span_singleton]
  rcases hπ.dvd_or_dvd hdiv with h1 | h1
  · exfalso
    have hne : Polynomial.C g.leadingCoeff ^ N ≠ 0 :=
      pow_ne_zero _ (Polynomial.C_ne_zero.2 (Polynomial.leadingCoeff_ne_zero.2 hg0))
    have h2 := Polynomial.natDegree_le_of_dvd h1 hne
    rw [← Polynomial.C_pow, Polynomial.natDegree_C] at h2
    omega
  · exact h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_exists_C_mem

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
