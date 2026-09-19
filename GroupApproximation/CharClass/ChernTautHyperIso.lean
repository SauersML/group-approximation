import GroupApproximation.CharClass.ChernTautRestrict
import GroupApproximation.CharClass.ThomHyperplaneLH

/-!
# `htaut`, in `cc-thom`'s presentation of the hyperplane

Lane `cc-projective` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.4, item 5).

`CharClass/ChernTautRestrict.lean` proves that the tautological class of `P(p ⊕ 1)`
restricts to the tautological class of `P(p)`, with the transport written as a
pullback along the inverse homeomorphism.  `cc-thom` states the same fact with the
transport written as `(ThomChernDeg.hyperIso p).hom`, the categorical isomorphism
built from the same homeomorphism.

The two are the same morphism: `TopCat.isoOfHomeo` takes `hom := TopCat.ofHom f`
and `cmap` *is* `TopCat.ofHom`.  So this file is the identity, and it exists only
so that neither side has to unfold the other's presentation at the use site.

## Main declarations

* `htaut_hyperIso` — **`htaut`** for `ThomChernDeg.thomData_total_of_taut`.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.CharClass.Bundle

noncomputable section

set_option linter.unusedSectionVars false

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **`htaut`.**  The tautological class of `P(p ⊕ 1)` restricts along the
hyperplane to the tautological class of `P(p)`, transported by `cc-thom`'s
`hyperIso`.  This is `pull_sInclusion_tautEulerOf` at a different spelling of the
same morphism. -/
theorem htaut_hyperIso [CompactSpace X] [T2Space X] (p : Bundle X ι) :
    pull (sInclusion (X := TopCat.of (Proj p.plusOne)) (Set.range (projIncl p))) 2
        (tautEulerOf p.plusOne)
      = pull (ThomChernDeg.hyperIso p).hom 2 (tautEulerOf p) :=
  pull_sInclusion_tautEulerOf p

end

end LH
end CharClass
end GroupApproximation
