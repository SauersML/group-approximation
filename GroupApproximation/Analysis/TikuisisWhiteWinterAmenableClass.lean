import GroupApproximation.Analysis.LanceNuclearAmenable
import GroupApproximation.Analysis.UCPContractiveMatrix
import GroupApproximation.Analysis.AmenableMFInput

/-!
# The amenable route, over one citation instead of four

`Analysis/TikuisisWhiteWinter` proves `amenable → operator-MF` over four
inputs: the ucp facts, Tikuisis--White--Winter, Lance and Tu.  Three of the
four are now gone.

* the ucp facts are `Quasidiagonal.ucpContractive`, **proved**
  (`Analysis/UCPContractiveMatrix`);
* Lance is `CStarExactness.amenableNuclearInput`, **proved**
  (`Analysis/LanceNuclearAmenable`);
* Tu is **eliminated**, not proved, and this file is where that happens.

## Why Tu can be eliminated

`TikuisisWhiteWinterInput` and `AmenableUCTInput` are both parameterised by an
abstract `UCT : Type u → Prop`, and the composite consumes them at the *same*
parameter.  The only work Tu does is to certify the UCT hypothesis of
Tikuisis--White--Winter for the algebras the route actually feeds it --- the
reduced algebras of countable amenable groups.  Instantiating the parameter at
exactly that class makes Tu's clause a tautology (`AmenableReducedClass` holds
of `C⋆_r(H)` by construction), and leaves the Tikuisis--White--Winter clause
saying: *a faithful trace on the reduced algebra of an amenable group is
quasidiagonal.*

That is a **weaker** hypothesis than the pair it replaces, not a stronger one:
given the real UCT predicate and Tu, it follows immediately.  So this is a
strict improvement in the citation surface, and no strength has been hidden ---
it has all moved into the one remaining row, which is the amenable case of
Tikuisis--White--Winter.

What is left, and it is genuinely left: **one** citation, the theorem of
Tikuisis--White--Winter, restricted to the algebras this development uses.

## Manuscript status

Discharges the Lance and Tu rows of `metadata/LITERATURE_QUARANTINE.md` (the
first by proof, the second by elimination) and reduces `AmenableMFInput` and
`CyclicBaseCalibration.AmenableImpliesMF` to a single citation.
-/

namespace GroupApproximation
namespace QuasidiagonalMF

open ReducedGroupCStarTrace

universe u

/-! ## The class of algebras the route actually uses -/

/-- The algebras the amenable route feeds to Tikuisis--White--Winter: the
reduced C⋆-algebras of countable amenable groups. -/
def AmenableReducedClass (A : Type u) : Prop :=
  ∃ (H : Type u) (inst : Group H),
    Amenability.IsAmenable H ∧ A = @ReducedGroupCStar H inst

/-- **Tu's input, at the class the route uses, is a tautology.**  This is the
elimination: nothing about the universal coefficient theorem is used, because
the parameter has been instantiated at the algebras whose UCT status Tu was
being cited for. -/
theorem amenableUCTInput_amenableReducedClass :
    AmenableUCTInput.{u} AmenableReducedClass.{u} where
  uct H inst hH := ⟨H, inst, hH, rfl⟩

/-! ## The route, over one citation -/

/-- **Every countable amenable group is operator-MF**, granting only the
Tikuisis--White--Winter theorem for reduced algebras of amenable groups.

Compare `isOperatorMF_of_isAmenable_of_tww`, which needs four inputs.  The
ucp facts and Lance are theorems of this repository; Tu is not used. -/
theorem isOperatorMF_of_isAmenable_of_twwAmenableClass
    (tww : TikuisisWhiteWinterInput.{u} AmenableReducedClass.{u})
    (G : Type u) [Group G] [Countable G]
    (hA : Amenability.IsAmenable G) :
    IsOperatorMF G :=
  isOperatorMF_of_isAmenable_of_tww Quasidiagonal.ucpContractive tww
    CStarExactness.amenableNuclearInput
    amenableUCTInput_amenableReducedClass G hA

/-- **`AmenableMFInput`, over one citation.**  The group-level corollary the
manuscript prints, with its literature surface reduced to the single row it
genuinely rests on. -/
theorem amenableMFInput_of_twwAmenableClass
    (tww : TikuisisWhiteWinterInput.{u} AmenableReducedClass.{u}) :
    AmenableMFInput.{u} where
  mf G _ _ hA := isOperatorMF_of_isAmenable_of_twwAmenableClass tww G hA

/-- The contrapositive, in the shape `sec:consequences` uses. -/
theorem not_isAmenable_of_not_isOperatorMF_of_twwAmenableClass
    (tww : TikuisisWhiteWinterInput.{u} AmenableReducedClass.{u})
    (G : Type u) [Group G] [Countable G] (hMF : ¬ IsOperatorMF G) :
    ¬ Amenability.IsAmenable G :=
  fun hA ↦ hMF (isOperatorMF_of_isAmenable_of_twwAmenableClass tww G hA)

end QuasidiagonalMF
end GroupApproximation
