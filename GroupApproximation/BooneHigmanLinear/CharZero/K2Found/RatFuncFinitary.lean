import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.LocFinitary
import GroupApproximation.BooneHigmanLinear.PaninAffine.Statements
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import GroupApproximation.Meta.AxiomGuard

/-!
# The finitary input for `F → F(T)` (k2-poly, piece F.5)

`ratFuncFinitaryAt : PaninAffine.RatFuncFinitaryAt F k r`, for every field `F` and all `k`, `r`.

`F(T)` is the localization of `F[T]` at the monic polynomials (`isLocalization_monic`). So
`F(T)[s₁..s_k][X]` is the localization of `F[T][s₁..s_k][X]` at the same monic polynomials
(`MvPolynomial.isLocalization`, `Polynomial.isLocalization`). By `exists_mem_ringMap_eq_one`, an
element of `St_r(F[s][X])` that dies over `F(T)` dies along every map that inverts one monic
`g ∈ F[T]`. `swapT` moves `T` from the coefficients to the outer variable, as in the statement.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found

-- Align the ring hierarchy used by coefficient maps with the one used by `ringMap`.
attribute [local instance 2000] CommSemiring.toSemiring CommRing.toRing CommRing.toCommSemiring

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open scoped Polynomial

section RatFunc

variable (F : Type) [Field F] (k : ℕ)

/-- The monic polynomials of `F[T]`. -/
def monicSubmonoid : Submonoid F[X] where
  carrier := {g | g.Monic}
  mul_mem' ha hb := Polynomial.Monic.mul ha hb
  one_mem' := Polynomial.monic_one

/-- `F(T)` is the localization of `F[T]` at the monic polynomials. -/
theorem isLocalization_monic : IsLocalization (monicSubmonoid F) (RatFunc F) :=
  (IsLocalization.iff_of_le_of_exists_dvd (M := monicSubmonoid F) (S := RatFunc F)
    (nonZeroDivisors F[X])
    (fun g hg => mem_nonZeroDivisors_of_ne_zero (show g.Monic from hg).ne_zero)
    fun n hn => ⟨n * Polynomial.C n.leadingCoeff⁻¹,
      Polynomial.monic_mul_leadingCoeff_inv (nonZeroDivisors.ne_zero hn),
      dvd_mul_right _ _⟩).mpr inferInstance

#audit_axioms isLocalization_monic

/-- `F[s][X] → F[T][s][X]`. -/
noncomputable def ratIota :
    Polynomial (MvPolynomial (Fin k) F) →+* Polynomial (MvPolynomial (Fin k) F[X]) :=
  Polynomial.mapRingHom (MvPolynomial.map Polynomial.C)

/-- `F[T][s][X] → F[s][X][T]`; `T` is the outer variable of the target. -/
noncomputable def swapT :
    Polynomial (MvPolynomial (Fin k) F[X]) →+* Polynomial (Polynomial (MvPolynomial (Fin k) F)) :=
  Polynomial.eval₂RingHom
    (MvPolynomial.eval₂Hom (Polynomial.mapRingHom
        ((Polynomial.C : MvPolynomial (Fin k) F →+* Polynomial (MvPolynomial (Fin k) F)).comp
          MvPolynomial.C))
      fun i => Polynomial.C (Polynomial.C (MvPolynomial.X i)))
    (Polynomial.C Polynomial.X)

theorem swapT_C_C (g : F[X]) :
    swapT F k (Polynomial.C (MvPolynomial.C g)) =
      g.map ((Polynomial.C : MvPolynomial (Fin k) F →+* Polynomial (MvPolynomial (Fin k) F)).comp
        MvPolynomial.C) := by
  simp only [swapT, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_C, Polynomial.coe_mapRingHom]

#audit_axioms swapT_C_C

theorem swapT_comp_ratIota :
    (swapT F k).comp (ratIota F k) =
      (Polynomial.C : Polynomial (MvPolynomial (Fin k) F) →+*
        Polynomial (Polynomial (MvPolynomial (Fin k) F))) := by
  have h0 : (MvPolynomial.eval₂Hom (Polynomial.mapRingHom
      ((Polynomial.C : MvPolynomial (Fin k) F →+* Polynomial (MvPolynomial (Fin k) F)).comp
        MvPolynomial.C))
      fun i => Polynomial.C (Polynomial.C (MvPolynomial.X i))).comp
        (MvPolynomial.map Polynomial.C) =
      (Polynomial.C : Polynomial (MvPolynomial (Fin k) F) →+*
        Polynomial (Polynomial (MvPolynomial (Fin k) F))).comp Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp
  apply Polynomial.ringHom_ext
  · intro b
    have h := RingHom.congr_fun h0 b
    simpa [swapT, ratIota] using h
  · simp [swapT, ratIota]

#audit_axioms swapT_comp_ratIota

end RatFunc

section Main

attribute [local instance] MvPolynomial.algebraMvPolynomial Polynomial.algebra

/-- **`RatFuncFinitaryAt`**, for every field `F` (board piece F.5). -/
theorem ratFuncFinitaryAt (F : Type) [Field F] (k r : ℕ) : PaninAffine.RatFuncFinitaryAt F k r := by
  intro y hy
  haveI := isLocalization_monic F
  have h1 : IsLocalization ((monicSubmonoid F).map (MvPolynomial.C (σ := Fin k)))
      (MvPolynomial (Fin k) (RatFunc F)) :=
    MvPolynomial.isLocalization (monicSubmonoid F) (RatFunc F)
  have h2 := Polynomial.isLocalization ((monicSubmonoid F).map (MvPolynomial.C (σ := Fin k)))
    (MvPolynomial (Fin k) (RatFunc F))
  have halg : algebraMap (Polynomial (MvPolynomial (Fin k) F[X]))
      (Polynomial (MvPolynomial (Fin k) (RatFunc F))) =
      Polynomial.mapRingHom (MvPolynomial.map (algebraMap F[X] (RatFunc F))) := rfl
  have hFC : (algebraMap F[X] (RatFunc F)).comp Polynomial.C = algebraMap F (RatFunc F) := by
    rw [IsScalarTower.algebraMap_eq F F[X] (RatFunc F), Polynomial.algebraMap_eq]
  have hcomp : (Polynomial.mapRingHom (MvPolynomial.map (algebraMap F[X] (RatFunc F)))).comp
      (ratIota F k) = Polynomial.mapRingHom (PaninAffine.ratFuncCoeff F k) := by
    rw [ratIota, Polynomial.mapRingHom_comp]
    congr 1
    apply RingHom.ext
    intro p
    rw [RingHom.comp_apply, MvPolynomial.map_map, hFC]
  have hu : ringMap (algebraMap (Polynomial (MvPolynomial (Fin k) F[X]))
      (Polynomial (MvPolynomial (Fin k) (RatFunc F)))) (ringMap (ratIota F k) y) = 1 := by
    rw [halg, ringMap_ringMap, hcomp]
    exact hy
  obtain ⟨m, hm, hfin⟩ := exists_mem_ringMap_eq_one _ (Fin r) h2 hu
  obtain ⟨m1, hm1, rfl⟩ := Submonoid.mem_map.mp hm
  obtain ⟨g, hg, rfl⟩ := Submonoid.mem_map.mp hm1
  refine ⟨g, hg, fun S _ φ hφ => ?_⟩
  have hunit : IsUnit ((φ.comp (swapT F k)) (Polynomial.C (MvPolynomial.C g))) := by
    rw [RingHom.comp_apply, swapT_C_C]
    exact hφ
  have h3 := hfin S (φ.comp (swapT F k)) hunit
  rwa [ringMap_ringMap, RingHom.comp_assoc, swapT_comp_ratIota] at h3

#audit_axioms ratFuncFinitaryAt

end Main

end K2Found
end BooneHigmanLinear
end GroupApproximation
