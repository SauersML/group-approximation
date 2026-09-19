import GroupApproximation.Algebra.IntJacobson
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# A field finitely generated as a ring is finite

Lemma 46.1 of the dossier.  The general Nullstellensatz over the Jacobson base
`ℤ` makes such a field integral over `ℤ`; characteristic zero is then impossible,
because `1/2` would be an integer, and in positive characteristic integrality
over the prime field together with finite generation makes the field a
finite-dimensional vector space over it.
-/

namespace GroupApproximation

universe u

/-- A field finitely generated as a `ℤ`-algebra is integral over `ℤ`. -/
theorem isIntegral_int_of_finiteType (k : Type u) [Field k]
    [h : Algebra.FiniteType ℤ k] : Algebra.IsIntegral ℤ k := by
  classical
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp h
  have hint := MvPolynomial.comp_C_integral_of_surjective_of_isJacobsonRing
    (R := ℤ) (σ := Fin n) (S := k) f.toRingHom hf
  have hcomp : (f.toRingHom.comp MvPolynomial.C) = algebraMap ℤ k := by
    ext r
    simp
  rw [hcomp] at hint
  exact ⟨fun x => hint x⟩

/-- Such a field cannot have characteristic zero: `1/2` would be an algebraic
integer inside `ℚ`. -/
theorem not_charZero_of_finiteType (k : Type u) [Field k]
    [Algebra.FiniteType ℤ k] : ¬ CharZero k := by
  intro hchar
  haveI := hchar
  haveI hint := isIntegral_int_of_finiteType k
  -- the rational `1/2`, viewed in `k`, is integral over `ℤ`
  have h2 : IsIntegral ℤ ((2 : ℚ)⁻¹ : ℚ) := by
    have hk : IsIntegral ℤ (algebraMap ℚ k ((2 : ℚ)⁻¹)) := hint.isIntegral _
    obtain ⟨P, hPmonic, hProot⟩ := hk
    refine ⟨P, hPmonic, ?_⟩
    have hinj : Function.Injective (algebraMap ℚ k) :=
      (algebraMap ℚ k).injective
    apply hinj
    rw [map_zero]
    have hpush : algebraMap ℚ k
          (Polynomial.eval₂ (algebraMap ℤ ℚ) ((2 : ℚ)⁻¹) P)
        = Polynomial.eval₂ (algebraMap ℤ k) (algebraMap ℚ k ((2 : ℚ)⁻¹)) P := by
      rw [Polynomial.hom_eval₂]
      congr 1
      exact Subsingleton.elim _ _
    rw [hpush]
    exact hProot
  -- but `ℤ` is integrally closed in `ℚ`
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  have hy2 : (y : ℚ) = 2⁻¹ := by simpa using hy
  have hmul : (2 : ℚ) * (y : ℚ) = 1 := by
    rw [hy2]
    norm_num
  have hyz : (2 : ℤ) * y = 1 := by exact_mod_cast hmul
  omega

/-- **Lemma 46.1, key step.**  A field finitely generated as a ring is finite.
The hypothesis is phrased as a surjection from a polynomial ring, which avoids
carrying an `Algebra ℤ` instance through the statement. -/
theorem finite_of_polynomial_surjective (k : Type u) [Field k] {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ →+* k) (hf : Function.Surjective f) :
    Finite k := by
  classical
  haveI : Algebra.FiniteType ℤ k :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mpr ⟨n, f.toIntAlgHom, hf⟩
  haveI hint := isIntegral_int_of_finiteType k
  obtain ⟨p, hp⟩ := CharP.exists k
  haveI := hp
  have hp0 : p ≠ 0 := by
    intro h
    subst h
    exact not_charZero_of_finiteType k (CharP.charP_to_charZero k)
  haveI hprime : Fact (Nat.Prime p) :=
    ⟨(CharP.char_is_prime_or_zero k p).resolve_right hp0⟩
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  haveI : IsScalarTower ℤ (ZMod p) k := by
    refine IsScalarTower.of_algebraMap_eq fun n => ?_
    have : algebraMap (ZMod p) k (algebraMap ℤ (ZMod p) n) = algebraMap ℤ k n := by
      have h1 : (algebraMap (ZMod p) k).comp (algebraMap ℤ (ZMod p))
          = algebraMap ℤ k := Subsingleton.elim _ _
      exact congrFun (congrArg (fun f : ℤ →+* k => (f : ℤ → k)) h1) n
    exact this.symm
  haveI : Algebra.IsIntegral (ZMod p) k := Algebra.IsIntegral.tower_top (R := ℤ)
  haveI : Algebra.FiniteType (ZMod p) k :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) k
  haveI : Module.Finite (ZMod p) k := Algebra.IsIntegral.finite
  exact Module.finite_of_finite (ZMod p)

end GroupApproximation
