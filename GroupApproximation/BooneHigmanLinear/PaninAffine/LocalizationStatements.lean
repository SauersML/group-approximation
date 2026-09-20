import GroupApproximation.BooneHigmanLinear.Tulenbaev.Components
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Away.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Localization interfaces for Steinberg excision and finitary descent

These definitions are shared by the finitary and excision proofs. Keeping them independent
of the geometric proof of Corollary 2.9 lets those foundational proofs compile independently.
-/

namespace GroupApproximation.BooneHigmanLinear.PaninAffine

open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman

/-- The canonical map `R_P → Frac R`. -/
noncomputable def fracMap {R : Type} [CommRing R] [IsDomain R] (P : Ideal R) [P.IsPrime] :
    Localization.AtPrime P →+* FractionRing R :=
  IsLocalization.lift (M := P.primeCompl) (g := algebraMap R (FractionRing R)) fun s =>
    IsUnit.mk0 _ (((IsFractionRing.injective R (FractionRing R)).ne_iff' (map_zero _)).mpr
      fun h0 => (show (s : R) ∉ P from s.2) (by rw [h0]; exact P.zero_mem))

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.fracMap

/-- The canonical map `R_s → R_P` for `s ∉ P`. -/
noncomputable def awayToAtPrime {R : Type} [CommRing R] (P : Ideal R) [P.IsPrime] {s : R}
    (hs : s ∉ P) : Localization.Away s →+* Localization.AtPrime P :=
  IsLocalization.Away.lift s
    (IsLocalization.map_units (Localization.AtPrime P) (⟨s, hs⟩ : P.primeCompl))

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.awayToAtPrime

/-- Zariski excision for `St_N`: compatible elements `(1, β)` over comaximal principal
localizations lift to `St_N(A)`. -/
def StZariskiExcisionAt (A : Type) [CommRing A] (N : ℕ) : Prop :=
  ∀ a b : A, a ∈ nonZeroDivisors A → b ∈ nonZeroDivisors A → IsCoprime a b →
    ∀ β : SteinbergGroup (Fin N) (Localization.Away b),
      ringMap (IsLocalization.Away.awayToAwayLeft b a :
          Localization.Away b →+* Localization.Away (a * b)) β = 1 →
        ∃ γ : SteinbergGroup (Fin N) A,
          ringMap (algebraMap A (Localization.Away a)) γ = 1 ∧
            ringMap (algebraMap A (Localization.Away b)) γ = β

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.StZariskiExcisionAt

/-- Finitary descent for Corollary 2.9: an element over `R_P[X]` killed over `Frac(R)[X]`
lifts over `R_g[X]`, `g ∉ P`, and is killed by inverting one nonzero element of `R`. -/
def Cor29FinitaryAt (R : Type) [CommRing R] [IsDomain R] (P : Ideal R) [P.IsPrime] (N : ℕ) :
    Prop :=
  ∀ α : SteinbergGroup (Fin N) (Polynomial (Localization.AtPrime P)),
    ringMap (Polynomial.mapRingHom (fracMap P)) α = 1 →
      ∃ (g : R) (hg : g ∉ P) (h : R), h ≠ 0 ∧
        ∃ α₁ : SteinbergGroup (Fin N) (Polynomial (Localization.Away g)),
          ringMap (S := Polynomial (Localization.AtPrime P))
            (Polynomial.mapRingHom (awayToAtPrime P hg)) α₁ = α ∧
            ringMap (S := Polynomial (Localization.Away (algebraMap R (Localization.Away g) h)))
              (Polynomial.mapRingHom (algebraMap (Localization.Away g)
                (Localization.Away (algebraMap R (Localization.Away g) h)))) α₁ = 1

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.Cor29FinitaryAt

end GroupApproximation.BooneHigmanLinear.PaninAffine
