import GroupApproximation.CharClass.GysinSphere
import GroupApproximation.CharClass.GysinCover
import GroupApproximation.CharClass.GysinPair
import GroupApproximation.CharClass.MayerVietorisSequence
import GroupApproximation.CharClass.BundleGysinData

/-!
# The pair of restrictions is bijective in the Gysin range

For the tautological line over `ℂP^d` the two pieces of the Gysin cover meet in a
space homotopy equivalent to the sphere bundle, which `cc-bundle`'s
`sphereCpTautHomeo` identifies with `unitVectors (Fin (d+1))`.  `GysinSphere` gives
that the cohomology of `S^{2d+1}`, so it vanishes in every degree strictly between
`0` and `2d+1`.

That is exactly the range the Gysin step needs, and no more.  `bijective_resPair`
at degree `2m+2` asks the intersection to vanish in degrees `2m+1` and `2m+2`, and
`cupPowE_ne_zero_of_pieces` asks for `m < d`, so the largest degree touched is `2d`.
The pair genuinely fails at the two ends — the intersection is connected, and it has
a top class in degree `2d+1` — which is why `GysinRanged` exists.

## Main declarations

* `gysinInterHomotopyEquivUnitVectors` — the intersection is the odd sphere.
* `bijective_resPair_cpTaut` — **the pair condition, in the range**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace Gysin

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59

noncomputable section

/-- **The intersection of the Gysin cover is the odd sphere.**  `cc-bundle` retracts
it onto the sphere bundle, and identifies that with the unit vectors. -/
def gysinInterHomotopyEquivUnitVectors (d : ℕ) :
    ContinuousMap.HomotopyEquiv
      ↥(mvInter (chartOpens (cpTaut d)) (notZeroOpens (cpTaut d)))
      ↥(unitVectors (Fin (d + 1))) :=
  (Bundle.interHomotopyEquivSphere (cpTaut d)).trans
    (Bundle.sphereCpTautHomeo d).toHomotopyEquiv

/-- The intersection has the cohomology of `S^{2d+1}`. -/
theorem hasSphereCohomology_gysinInter (d : ℕ) :
    HasSphereCohomology
      (mvInter (chartOpens (cpTaut d)) (notZeroOpens (cpTaut d)))
      (2 * d + 1) := by
  refine HasSphereCohomology.of_linearEquiv
    (fun k => (pullEquivOfHomotopyEquiv (gysinInterHomotopyEquivUnitVectors d) k).symm) ?_
  exact hasSphereCohomology_unitVectors d

/-- **The pair of restrictions is bijective in the Gysin range.**  Degree `2m+2` for
`m < d`, which is where the intersection is acyclic; at `m = d` the intersection's
top class appears and the statement is false. -/
theorem bijective_resPair_cpTaut (d m : ℕ) (hm : m < d) :
    Function.Bijective
      (fun z : Hmod2 (TopCat.of (Bundle.Proj (cpTaut d).plusOne)) (2 * m + 2) =>
        ((mvSequence (chartOpens (cpTaut d)) (notZeroOpens (cpTaut d))
            (chartOpens_sup_notZeroOpens (cpTaut d))).resU (2 * m + 2) z,
          (mvSequence (chartOpens (cpTaut d)) (notZeroOpens (cpTaut d))
            (chartOpens_sup_notZeroOpens (cpTaut d))).resV (2 * m + 2) z)) := by
  have hW := hasSphereCohomology_gysinInter d
  exact bijective_resPair _ (2 * m + 1)
    (fun w => hW.2.2 (2 * m + 1) (by omega) (by omega) w)
    (fun w => hW.2.2 (2 * m + 2) (by omega) (by omega) w)

end

end Gysin
end CharClass
end GroupApproximation
