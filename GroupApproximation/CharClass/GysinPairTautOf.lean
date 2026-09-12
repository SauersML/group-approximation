import GroupApproximation.CharClass.GysinPairTaut
import GroupApproximation.CharClass.GysinSphereOf
import GroupApproximation.CharClass.MayerVietorisSequenceOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The Gysin pair condition for the tautological bundle, over a field

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

`GysinPairTaut.lean` shows, at `F₂`, that the pair of Mayer–Vietoris restrictions of
`P(taut ⊕ 1)` to the chart and to the complement of the zero section is bijective in the
Gysin range, because the intersection is the odd sphere `S^{2d+1}`.  Over a field `K` the
intersection is still homotopy equivalent to the unit vectors (pure topology), the unit
vectors have the `K`-cohomology of the odd sphere (`GysinSphereOf`), and
`GysinPair.bijective_resPair` is already stated over any `MVSequenceOf K`.  The sequence is
`lix-lh`'s `mvSequenceOf K`.

## Main declarations

* `hasSphereCohomologyOf_gysinInter` — the intersection of the cover, over a field.
* `bijective_resPair_cpTautOf` — **the pair of restrictions is bijective in the Gysin range**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace Gysin

open CategoryTheory
open GroupApproximation.STW59

noncomputable section

/-- The intersection of the Gysin cover has the `K`-cohomology of `S^{2d+1}`. -/
theorem hasSphereCohomologyOf_gysinInter (K : Type) [Field K] (d : ℕ) :
    HasSphereCohomologyOf K
      (mvInter (chartOpens (cpTaut d)) (notZeroOpens (cpTaut d)))
      (2 * d + 1) := by
  refine HasSphereCohomologyOf.of_linearEquiv
    (fun k => (pullEquivOfHomotopyEquivOf K (gysinInterHomotopyEquivUnitVectors d) k).symm) ?_
  exact hasSphereCohomologyOf_unitVectors K d

/-- **The pair of restrictions is bijective in the Gysin range, over a field.**  Degree
`2m+2` for `m < d`, where the intersection is acyclic. -/
theorem bijective_resPair_cpTautOf (K : Type) [Field K] (d m : ℕ) (hm : m < d) :
    Function.Bijective
      (fun z : Hmod K (TopCat.of (Bundle.Proj (cpTaut d).plusOne)) (2 * m + 2) =>
        ((mvSequenceOf K (chartOpens (cpTaut d)) (notZeroOpens (cpTaut d))
            (chartOpens_sup_notZeroOpens (cpTaut d))).resU (2 * m + 2) z,
          (mvSequenceOf K (chartOpens (cpTaut d)) (notZeroOpens (cpTaut d))
            (chartOpens_sup_notZeroOpens (cpTaut d))).resV (2 * m + 2) z)) := by
  have hW := hasSphereCohomologyOf_gysinInter K d
  exact bijective_resPair _ (2 * m + 1)
    (fun w => hW.2.2 (2 * m + 1) (by omega) (by omega) w)
    (fun w => hW.2.2 (2 * m + 2) (by omega) (by omega) w)

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms bijective_resPair_cpTautOf

end

end Gysin
end CharClass
end GroupApproximation
