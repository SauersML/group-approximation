import GroupApproximation.CharClass.LerayHirschChartClassGen
import GroupApproximation.CharClass.ChernEulerBundleOf

/-!
# The tautological class of a projectivised bundle of any rank, with coefficients in `K`

The coefficient-generic twins of `LerayHirschChartClassGen.tautEulerOf`, `tautEulerDual` and
`ChernSliceNaturality.tautEulerOf_comap`.  Over `K` the degree-2 generator of the target
projective space is data (`ChernEulerBundleOf`), so every class here takes a chosen
`hgen ∈ H^2(ℂP^{1 + card ι}; K)`; at `F₂` with the canonical generator the classes are the `F₂`
ones on the nose.

The dual class `tautEulerDualK = −tautEulerOfK` is `e(O(1))`, the class the Grothendieck relation
`∏ (ξ + a_i) = 0` is stated with over any ring (`ChernRelation`'s `Conventions` block).

## Main declarations

* `LH.tautEulerOfK`, `LH.tautEulerDualK`, `LH.tautEulerOf_eq_tautEulerOfK`.
* `LH.tautEulerOf_comapOf`, `LH.tautEulerDual_comapOf` — naturality under pulling the bundle back.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.CPn

noncomputable section

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The class `ξ` over `K`** for a projectivised bundle of any rank: the Euler class of its
tautological line, at an index large enough to compare with `ℂP^r`, relative to `hgen`. -/
def tautEulerOfK (K : Type) [CommRing K] (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2)
    (p : Bundle X ι) : Hmod K (TopCat.of (Proj p)) 2 :=
  eulerOfBundleOf K hgen (pushforward (tautEmbOf ι) (tautEmbOf_injective ι) (tautLine p))
    (trace_pushforward_one (tautEmbOf ι) (tautEmbOf_injective ι) (tautLine p)
      (trace_tautLine p))

/-- **The dual tautological class over `K`**, `ξ = e(O(1)) = −e(O(−1))`. -/
def tautEulerDualK (K : Type) [CommRing K] (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2)
    (p : Bundle X ι) : Hmod K (TopCat.of (Proj p)) 2 :=
  -tautEulerOfK K hgen p

/-- At `F₂`, with the canonical generator, this is `tautEulerOf`. -/
theorem tautEulerOf_eq_tautEulerOfK (p : Bundle X ι) :
    tautEulerOf p
      = tautEulerOfK (ZMod 2) (cpGen (1 + tautCardOf ι) (show 1 ≤ 1 + tautCardOf ι by omega))
          p :=
  rfl

/-- **Naturality of the tautological class over `K`.**  Pulling the bundle back along `f`
pulls the class back along the induced map of projectivisations. -/
theorem tautEulerOf_comapOf (K : Type) [CommRing K] (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2)
    (f : C(Y, X)) (q : Bundle X ι) :
    pull (cmap (projComap f q)) 2 (tautEulerOfK K hgen q) = tautEulerOfK K hgen (comap f q) :=
  (eulerOfBundle_comapOf K hgen
    (pushforward (tautEmbOf ι) (tautEmbOf_injective ι) (tautLine q))
    (trace_pushforward_one (tautEmbOf ι) (tautEmbOf_injective ι) (tautLine q)
      (trace_tautLine q))
    (projComap f q)).symm

/-- **Naturality of the dual tautological class over `K`.** -/
theorem tautEulerDual_comapOf (K : Type) [CommRing K]
    (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2) (f : C(Y, X)) (q : Bundle X ι) :
    pull (cmap (projComap f q)) 2 (tautEulerDualK K hgen q)
      = tautEulerDualK K hgen (comap f q) := by
  rw [tautEulerDualK, tautEulerDualK, ← tautEulerOf_comapOf K hgen f q]
  exact map_neg (pullLinear (K := K) (cmap (projComap f q)) 2) (tautEulerOfK K hgen q)

end

end LH
end CharClass
end GroupApproximation
