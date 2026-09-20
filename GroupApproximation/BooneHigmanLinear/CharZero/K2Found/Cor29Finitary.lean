import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.LocFinitary
import GroupApproximation.BooneHigmanLinear.PaninAffine.LocalizationStatements
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.PolynomialAlgebra
import GroupApproximation.Meta.AxiomGuard

/-!
# The finitary step of LSV Cor 2.9 (k2-poly, piece F.5)

`cor29FinitaryAt : PaninAffine.Cor29FinitaryAt R P N` for every domain `R` and prime `P`.

* `R_P[X]` is the localization of `R[X]` at `C(R ∖ P)` (`Polynomial.isLocalization`). By
  `exists_mem_ringMap_eq`, `α ∈ St_N(R_P[X])` comes from `St_N(R[X][1/C g])` for some `g ∉ P`,
  hence from `α₁ ∈ St_N(R_g[X])` (`awayCMap`).
* `Frac(R)[X]` is the localization of `R_g[X]` at `C(R_g⁰)`. By `exists_mem_ringMap_eq_one`,
  `α₁` dies once one `h' ∈ R_g⁰` is inverted. Write `h' g^n = h` with `h ∈ R`, `h ≠ 0`; then
  inverting `h` inverts `h'`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found

-- Use the same ring hierarchy for polynomial/localization maps and `algebraMap`.
attribute [local instance 2000] CommSemiring.toSemiring CommRing.toRing CommRing.toCommSemiring

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open scoped Polynomial

section Cor29

variable {R : Type} [CommRing R]

/-- `R[X][1/C g] → R_g[X]`. -/
noncomputable def awayCMap (g : R) :
    Localization.Away (Polynomial.C g) →+* Polynomial (Localization.Away g) :=
  IsLocalization.Away.lift (Polynomial.C g)
    (g := Polynomial.mapRingHom (algebraMap R (Localization.Away g))) (by
      rw [Polynomial.coe_mapRingHom, Polynomial.map_C]
      exact (IsLocalization.Away.algebraMap_isUnit g).map Polynomial.C)

theorem awayCMap_comp (g : R) :
    (awayCMap g).comp (algebraMap R[X] (Localization.Away (Polynomial.C g))) =
      Polynomial.mapRingHom (algebraMap R (Localization.Away g)) :=
  IsLocalization.Away.lift_comp _ _

#audit_axioms awayCMap_comp

attribute [local instance] Polynomial.algebra

variable (P : Ideal R) [P.IsPrime]

/-- An element over `R_P[X]` is defined over one coefficient localization `R_g[X]`. -/
theorem exists_away_polynomial_lift (N : ℕ)
    (α : SteinbergGroup (Fin N) (Polynomial (Localization.AtPrime P))) :
    ∃ (g : R) (hg : g ∉ P),
      ∃ α₁ : SteinbergGroup (Fin N) (Polynomial (Localization.Away g)),
        ringMap (Polynomial.mapRingHom (PaninAffine.awayToAtPrime P hg)) α₁ = α := by
  have hL1 := Polynomial.isLocalization P.primeCompl (Localization.AtPrime P)
  obtain ⟨m, hm, u, f, hf, hu⟩ := exists_mem_ringMap_eq _ (Fin N) hL1 α
  obtain ⟨g, hgP, rfl⟩ := Submonoid.mem_map.mp hm
  have hg : g ∉ P := hgP
  have haw : (PaninAffine.awayToAtPrime P hg).comp (algebraMap R (Localization.Away g)) =
      algebraMap R (Localization.AtPrime P) :=
    IsLocalization.Away.lift_comp _ _
  have hA : (Polynomial.mapRingHom (PaninAffine.awayToAtPrime P hg)).comp (awayCMap g) = f := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.C g))
    rw [RingHom.comp_assoc, awayCMap_comp, Polynomial.mapRingHom_comp, haw, hf,
      Polynomial.algebraMap_def]
  have hα₁ : ringMap (Polynomial.mapRingHom (PaninAffine.awayToAtPrime P hg))
      (ringMap (awayCMap g) u) = α := by
    rw [ringMap_ringMap, hA, hu]
  exact ⟨g, hg, ringMap (awayCMap g) u, hα₁⟩

#audit_axioms exists_away_polynomial_lift

variable [IsDomain R]

/-- An element over `R_g[X]` that dies over the fraction field dies after inverting one
nonzero element of the original coefficient ring. -/
theorem exists_away_fraction_death (N : ℕ) (g : R) (hg : g ∉ P)
    (α₁ : SteinbergGroup (Fin N) (Polynomial (Localization.Away g)))
    (hα₁ : ringMap (Polynomial.mapRingHom
      ((PaninAffine.fracMap P).comp (PaninAffine.awayToAtPrime P hg))) α₁ = 1) :
    ∃ r : R, r ≠ 0 ∧
      ringMap (S := Polynomial (Localization.Away (algebraMap R (Localization.Away g) r)))
        (Polynomial.mapRingHom (algebraMap (Localization.Away g)
          (Localization.Away (algebraMap R (Localization.Away g) r)))) α₁ = 1 := by
  have haw : (PaninAffine.awayToAtPrime P hg).comp (algebraMap R (Localization.Away g)) =
      algebraMap R (Localization.AtPrime P) :=
    IsLocalization.Away.lift_comp _ _
  -- `Frac R` as an `R_g`-algebra.
  have hg0 : g ≠ 0 := fun h0 => hg (h0 ▸ P.zero_mem)
  have hgF : IsUnit (algebraMap R (FractionRing R) g) := IsUnit.mk0 _ (by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))]
    exact hg0)
  letI : Algebra (Localization.Away g) (FractionRing R) :=
    (IsLocalization.Away.lift g hgF).toAlgebra
  haveI : IsScalarTower R (Localization.Away g) (FractionRing R) :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.Away.lift_comp g hgF).symm
  haveI : IsFractionRing (Localization.Away g) (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers g)
      (Localization.Away g) (FractionRing R)
  haveI : Nontrivial (Localization.Away g) :=
    (algebraMap (Localization.Away g) (FractionRing R)).domain_nontrivial
  have hfracP : (PaninAffine.fracMap P).comp (algebraMap R (Localization.AtPrime P)) =
      algebraMap R (FractionRing R) :=
    IsLocalization.lift_comp _
  have hfr : (PaninAffine.fracMap P).comp (PaninAffine.awayToAtPrime P hg) =
      algebraMap (Localization.Away g) (FractionRing R) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    rw [RingHom.comp_assoc, haw, hfracP]
    exact IsScalarTower.algebraMap_eq _ _ _
  -- `α₁` dies once some `h' ∈ R_g⁰` is inverted.
  have h2 := Polynomial.isLocalization (nonZeroDivisors (Localization.Away g)) (FractionRing R)
  have hu2 : ringMap (algebraMap (Localization.Away g)[X] (FractionRing R)[X])
      α₁ = 1 := by
    rw [Polynomial.algebraMap_def, ← hfr]
    exact hα₁
  obtain ⟨m', hm', hfin⟩ := exists_mem_ringMap_eq_one _ (Fin N) h2 hu2
  obtain ⟨h', hh', rfl⟩ := Submonoid.mem_map.mp hm'
  obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj g h'
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero] at hr
    exact nonZeroDivisors.ne_zero hh'
      ((IsLocalization.Away.algebraMap_pow_isUnit g n).mul_left_eq_zero.mp hr)
  refine ⟨r, hr0, ?_⟩
  apply hfin
  rw [Polynomial.coe_mapRingHom, Polynomial.map_C]
  apply IsUnit.map
  have h1 := congrArg (algebraMap (Localization.Away g)
    (Localization.Away (algebraMap R (Localization.Away g) r))) hr
  rw [map_mul] at h1
  have hunit : IsUnit (algebraMap (Localization.Away g)
      (Localization.Away (algebraMap R (Localization.Away g) r)) h' *
      algebraMap (Localization.Away g) (Localization.Away (algebraMap R (Localization.Away g) r))
        (algebraMap R (Localization.Away g) g ^ n)) := by
    rw [h1]
    exact IsLocalization.Away.algebraMap_isUnit _
  exact isUnit_of_mul_isUnit_left hunit

#audit_axioms exists_away_fraction_death

/-- **`Cor29FinitaryAt`** for every domain and prime (board piece F.5). -/
theorem cor29FinitaryAt (N : ℕ) : PaninAffine.Cor29FinitaryAt R P N := by
  intro α hα
  obtain ⟨g, hg, α₁, hα₁⟩ := exists_away_polynomial_lift P N α
  have hdeath : ringMap (Polynomial.mapRingHom
      ((PaninAffine.fracMap P).comp (PaninAffine.awayToAtPrime P hg))) α₁ = 1 := by
    rw [← Polynomial.mapRingHom_comp, ← ringMap_ringMap, hα₁, hα]
  obtain ⟨r, hr, hkill⟩ := exists_away_fraction_death P N g hg α₁ hdeath
  exact ⟨g, hg, r, hr, α₁, hα₁, hkill⟩

#audit_axioms cor29FinitaryAt

end Cor29

end K2Found
end BooneHigmanLinear
end GroupApproximation
