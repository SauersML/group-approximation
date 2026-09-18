import Mathlib.Algebra.Ring.Int.Field
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Localization.Away.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Maximal ideals of `ℤ[1/m][s_1..s_k]` have positive residue characteristic

Lane `bh-met-74`, helper module (pure commutative algebra, no `K₂`).  Every maximal ideal `𝔪`
of `B = ℤ[1/m][s_1..s_k]` contains a rational prime `p`; in other words the residue field
`B ⧸ 𝔪` has characteristic `p > 0` (it is in fact finite, but only `p ∈ 𝔪` is used).

* `czCubeLocal_isJacobsonRing_int`: `ℤ` is a Jacobson ring.  A prime ideal of `ℤ` is `(p)`,
  which is maximal, or `⊥`; an integer `x` lying in every maximal ideal is divisible by a
  prime `q > |x|`, so `x = 0`.
* `czCubeLocal_isJacobsonRing_away`: so is `ℤ[1/m]` (`isJacobsonRing_localization`).
* `czCubeLocal_isMaximal_comap_C`: over a Jacobson ring `A`, a maximal ideal of
  `A[s_1..s_k]` contracts to a maximal ideal of `A` (`A → A[s] ⧸ 𝔪` is integral,
  `MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing`).
* `czCubeLocal_exists_prime_mem_away`: a maximal ideal of `ℤ[1/m]` contracts to a maximal ideal
  of `ℤ` (`IsLocalization.isMaximal_iff_isMaximal_disjoint`), which is `(p)`, `p` prime.
* `czCubeLocal_exists_prime_mem_mvPolynomial`, `czCubeLocal_exists_prime_mem`: hence every
  maximal ideal of `ℤ[1/m][s_1..s_k]` contains some prime `p`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

/-- `ℤ` is a Jacobson ring. -/
theorem czCubeLocal_isJacobsonRing_int : IsJacobsonRing ℤ := by
  refine isJacobsonRing_iff_prime_eq.mpr fun P hP => ?_
  rcases Ideal.isPrime_int_iff.mp hP with rfl | ⟨p, hp, rfl⟩
  · refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    obtain ⟨q, hxq, hq⟩ := Nat.exists_infinite_primes (x.natAbs + 1)
    have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
      @Int.ideal_span_isMaximal_of_prime q ⟨hq⟩
    have hle : Ideal.jacobson (⊥ : Ideal ℤ) ≤ Ideal.span {(q : ℤ)} := sInf_le ⟨bot_le, hmax⟩
    have hdvd : (q : ℤ) ∣ x := Ideal.mem_span_singleton.mp (hle hx)
    rw [Ideal.mem_bot]
    exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by rw [Int.natAbs_natCast]; omega)
  · have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      @Int.ideal_span_isMaximal_of_prime p ⟨hp⟩
    exact Ideal.jacobson_eq_self_of_isMaximal (H := hmax)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeLocal_isJacobsonRing_int

/-- `ℤ[1/m]` is a Jacobson ring. -/
theorem czCubeLocal_isJacobsonRing_away (m : ℤ) : IsJacobsonRing (Localization.Away m) :=
  haveI : IsJacobsonRing ℤ := czCubeLocal_isJacobsonRing_int
  isJacobsonRing_localization m

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeLocal_isJacobsonRing_away

/-- Over a Jacobson ring `A`, a maximal ideal of `A[s_1..s_k]` contracts to a maximal ideal
of `A`. -/
theorem czCubeLocal_isMaximal_comap_C {A : Type*} [CommRing A] [IsJacobsonRing A] {k : ℕ}
    (P : Ideal (MvPolynomial (Fin k) A)) [hP : P.IsMaximal] :
    (P.comap (MvPolynomial.C : A →+* MvPolynomial (Fin k) A)).IsMaximal := by
  have hbot : (⊥ : Ideal (MvPolynomial (Fin k) A ⧸ P)).IsMaximal :=
    (Ideal.bot_quotient_isMaximal_iff P).mpr hP
  have h := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'
    ((Ideal.Quotient.mk P).comp (MvPolynomial.C : A →+* MvPolynomial (Fin k) A))
    (MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing P) ⊥
  rwa [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeLocal_isMaximal_comap_C

/-- Every maximal ideal of `ℤ[1/m]` contains a prime `p`. -/
theorem czCubeLocal_exists_prime_mem_away (m : ℤ) (P : Ideal (Localization.Away m))
    (hP : P.IsMaximal) : ∃ p : ℕ, p.Prime ∧ (p : Localization.Away m) ∈ P := by
  haveI : IsJacobsonRing ℤ := czCubeLocal_isJacobsonRing_int
  obtain ⟨hI, -⟩ :=
    (IsLocalization.isMaximal_iff_isMaximal_disjoint (Localization.Away m) m P).mp hP
  rcases Ideal.isPrime_int_iff.mp hI.isPrime with hbot | ⟨p, hp, hspan⟩
  · exact absurd hbot (Ring.ne_bot_of_isMaximal_of_not_isField hI Int.not_isField)
  · refine ⟨p, hp, ?_⟩
    have hmem : (p : ℤ) ∈ P.under ℤ := by
      rw [hspan]
      exact Ideal.mem_span_singleton_self _
    have h : algebraMap ℤ (Localization.Away m) (p : ℤ) ∈ P := Ideal.mem_comap.mp hmem
    rwa [map_natCast] at h

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeLocal_exists_prime_mem_away

/-- Over a Jacobson ring `A` whose maximal ideals each contain a prime, every maximal ideal of
`A[s_1..s_k]` contains a prime. -/
theorem czCubeLocal_exists_prime_mem_mvPolynomial {A : Type*} [CommRing A] [IsJacobsonRing A]
    (hA : ∀ P : Ideal A, P.IsMaximal → ∃ p : ℕ, p.Prime ∧ (p : A) ∈ P) {k : ℕ}
    (P : Ideal (MvPolynomial (Fin k) A)) (hP : P.IsMaximal) :
    ∃ p : ℕ, p.Prime ∧ (p : MvPolynomial (Fin k) A) ∈ P := by
  obtain ⟨p, hp, hpm⟩ := hA _ (czCubeLocal_isMaximal_comap_C P)
  refine ⟨p, hp, ?_⟩
  have h : (MvPolynomial.C : A →+* MvPolynomial (Fin k) A) (p : A) ∈ P := Ideal.mem_comap.mp hpm
  rwa [map_natCast] at h

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeLocal_exists_prime_mem_mvPolynomial

/-- **Every maximal ideal of `ℤ[1/m][s_1..s_k]` contains a prime `p`.** -/
theorem czCubeLocal_exists_prime_mem (m : ℤ) {k : ℕ}
    (P : Ideal (MvPolynomial (Fin k) (Localization.Away m))) (hP : P.IsMaximal) :
    ∃ p : ℕ, p.Prime ∧ (p : MvPolynomial (Fin k) (Localization.Away m)) ∈ P :=
  haveI : IsJacobsonRing (Localization.Away m) := czCubeLocal_isJacobsonRing_away m
  czCubeLocal_exists_prime_mem_mvPolynomial (czCubeLocal_exists_prime_mem_away m) P hP

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubeLocal_exists_prime_mem

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
