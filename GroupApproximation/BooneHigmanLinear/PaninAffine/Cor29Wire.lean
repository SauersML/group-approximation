import GroupApproximation.BooneHigmanLinear.PaninAffine.Cor29Finitary
import GroupApproximation.BooneHigmanLinear.PaninAffine.Main
import GroupApproximation.BooneHigmanLinear.K2Poly.LSVForm
import GroupApproximation.Meta.AxiomGuard

/-!
# LSV Cor 2.9 as `K2Poly.NKFieldInjAt` (lane k2-panin)

This module restates `PaninAffine.Cor29Finitary.eq_one_of_fracMap_of_geometry` in the form that
`K2Poly.LSVForm.unstableNKPoly_of_LSV` consumes (`hCor29`). The field is `E = Frac R` and the map
is `ι = fracMap M : R_M → Frac R`. The hypotheses `K₂` and `u(0) = 1` of `NKFieldInjAt` are not
used, since the injectivity holds on all of `St_r(R_M[X])`. Over an infinite field the geometric
input is `PaninAffine.Main.infiniteFieldAffineMonicFibre`. What remains is Zariski excision
(F.4) and monic injectivity (H.b, non-FR). Not root-wired.
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
    (M : Ideal (MvPolynomial (Fin k) K)) [M.IsMaximal] :
    K2Poly.NKFieldInjAt (Localization.AtPrime M) r :=
  ⟨FractionRing (MvPolynomial (Fin k) K), inferInstance, fracMap M, fun u _ hu =>
    eq_one_of_fracMap_of_geometry hGeo hExc hMon M _ hu⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.nkFieldInjAt_of_geometry

/-- **LSV Cor 2.9 over an infinite field**: only F.4 and H.b remain. -/
theorem nkFieldInjAt_of_infinite {K : Type} [Field K] [Infinite K] {k r : ℕ}
    (hExc : ∀ (A : Type) [CommRing A], StZariskiExcisionAt A r)
    (hMon : ∀ (A : Type) [CommRing A], TulenbaevHorrocks.StMonicInjAt A r)
    (M : Ideal (MvPolynomial (Fin k) K)) [M.IsMaximal] :
    K2Poly.NKFieldInjAt (Localization.AtPrime M) r :=
  nkFieldInjAt_of_geometry (infiniteFieldAffineMonicFibre K) hExc hMon M

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.nkFieldInjAt_of_infinite

end PaninAffine
end BooneHigmanLinear
end GroupApproximation
