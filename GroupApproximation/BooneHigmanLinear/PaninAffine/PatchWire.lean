import GroupApproximation.BooneHigmanLinear.PaninAffine.Patching
import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.TulXInst
import GroupApproximation.Meta.AxiomGuard

/-!
# F.4 from van der Kallen's elements (lane k2-panin)

This module composes two results:
* `PaninAffine.Patching.stZariskiExcisionAt_of_tulX`: Tulenbaev's Prop 1.4(b) from `TulX r`;
* `K2Found.TulElem.tulX_of_elements` (bh-pal-linear-char0): `TulX r` from van der Kallen's elements
  (T 1.1–1.3).

Zariski excision for `St_r`, `r ≥ 5`, therefore waits only on k2-vdk's construction. That
construction must give elements `E B` for every ring `B` that are local (`TulElem.IsLocal`) and
natural in ring maps (`TulElem.EltNatural`). Not root-wired.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace PaninAffine

open GroupApproximation.BooneHigmanLinear.K2Found

/-- **F.4 from van der Kallen's elements.** -/
theorem stZariskiExcisionAt_of_elements {r : ℕ}
    (E : ∀ (B : Type) [CommRing B], VdK.Elements (Fin r) B)
    [∀ (B : Type) [CommRing B], Fact (TulElem.IsLocal (E B))]
    (hnat : ∀ (B C : Type) [CommRing B] [CommRing C] (f : B →+* C),
      TulElem.EltNatural (E B) (E C) f)
    (h5 : 5 ≤ r) (A : Type) [CommRing A] : StZariskiExcisionAt A r :=
  stZariskiExcisionAt_of_tulX (TulElem.tulX_of_elements E hnat h5) h5 A

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.stZariskiExcisionAt_of_elements

end PaninAffine
end BooneHigmanLinear
end GroupApproximation
