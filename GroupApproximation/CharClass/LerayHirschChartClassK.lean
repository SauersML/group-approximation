import GroupApproximation.CharClass.LerayHirschChartClass
import GroupApproximation.CharClass.ChernEulerBundleOf

/-!
# The tautological class of `P(p ⊕ 1)` with coefficients in `K`

The coefficient-generic twin of `LerayHirschChartClass.tautEuler`: the Euler class, over `K`, of
the tautological line of `P(p ⊕ 1)`, pushed into a `Fin` large enough to descend from, relative
to a chosen class `hgen ∈ H^2(ℂP^{1 + tautCard ι}; K)` (over `K` the generator is data; see
`ChernEulerBundleOf`).  At `F₂` with the canonical generator it is `tautEuler` on the nose.

The name is `tautEulerK`, not `tautEulerOf`: `LerayHirschChartClassGen.tautEulerOf` is already the
`F₂` class at a general index.

## Main declarations

* `LH.tautEulerK` — the class over `K`.
* `LH.tautEuler_eq_tautEulerK` — the `F₂` bridge.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.CPn

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The class `ξ` over `K`**: the Euler class of the tautological line of `P(p ⊕ 1)`, taken at
an index large enough to compare with `ℂP¹`, relative to the chosen class `hgen`. -/
def tautEulerK (K : Type) [CommRing K] (hgen : Hmod K (CPtop (1 + tautCard ι)) 2)
    (p : Bundle X ι) : Hmod K (TopCat.of (Proj p.plusOne)) 2 :=
  eulerOfBundleOf K hgen
    (pushforward (tautEmb ι) (tautEmb_injective ι) (tautLine p.plusOne))
    (trace_pushforward_one (tautEmb ι) (tautEmb_injective ι) (tautLine p.plusOne)
      (trace_tautLine p.plusOne))

/-- At `F₂`, with the canonical generator, this is `tautEuler`. -/
theorem tautEuler_eq_tautEulerK (p : Bundle X ι) :
    tautEuler p
      = tautEulerK (ZMod 2) (cpGen (1 + tautCard ι) (show 1 ≤ 1 + tautCard ι by omega)) p :=
  rfl

end

end LH
end CharClass
end GroupApproximation
