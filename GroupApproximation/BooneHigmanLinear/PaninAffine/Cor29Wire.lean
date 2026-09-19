import GroupApproximation.BooneHigmanLinear.PaninAffine.Cor29
import GroupApproximation.BooneHigmanLinear.K2Poly.LSVForm
import GroupApproximation.Meta.AxiomGuard

/-!
# LSV Cor 2.9 as `K2Poly.NKFieldInjAt` (lane k2-panin)

`PaninAffine.Cor29.eq_one_of_fracMap`, stated in the form that
`K2Poly.LSVForm.unstableNKPoly_of_LSV` consumes (`hCor29`). The field is `E = Frac R` and the map
is `ι = fracMap M : R_M → Frac R`. The hypotheses `K₂` and `u(0) = 1` of `NKFieldInjAt` are not
used: the injectivity holds on all of `St_r(R_M[X])`. Not root-wired.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace PaninAffine

open GroupApproximation.BooneHigman

/-- **LSV Cor 2.9 for `K[s₁..s_k]`, `NKFieldInjAt` form.** -/
theorem nkFieldInjAt_of_geometry {K : Type} [Field K] {k r : ℕ}
    (hGeo : AffineMonicFibreStatement K)
    (hExc : ∀ (A : Type) [CommRing A], StZariskiExcisionAt A r)
    (hMon : ∀ (A : Type) [CommRing A], TulenbaevHorrocks.StMonicInjAt A r)
    (M : Ideal (MvPolynomial (Fin k) K)) [M.IsMaximal]
    (hFin : Cor29FinitaryAt (MvPolynomial (Fin k) K) M r) :
    K2Poly.NKFieldInjAt (Localization.AtPrime M) r :=
  ⟨FractionRing (MvPolynomial (Fin k) K), inferInstance, fracMap M, fun u _ hu =>
    eq_one_of_fracMap hGeo hExc hMon M hFin _ hu⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.nkFieldInjAt_of_geometry

end PaninAffine
end BooneHigmanLinear
end GroupApproximation
