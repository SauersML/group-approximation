import GroupApproximation.Manuscript.NinetyNineProblems.FactorizationImpliesHyperlinear
import GroupApproximation.Analysis.AmenableTraceHyperlinear
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown's implication, discharged

`Manuscript/NinetyNineProblems/FactorizationImpliesHyperlinear.lean` states
Brown, *Invariant means and finite representation theory of C⋆-algebras*,
Mem. Amer. Math. Soc. **184** (2006), no. 865, Theorem 3.1.7 `(1) ⟹ (2)` --- a
group with Kirchberg's factorization property is hyperlinear --- as the typed
input `BrownAmenableTraceHyperlinearInput`, and its docstring records what a
proof would need: the **Hilbert--Schmidt polar correction**, an approximately
unitary matrix being close to a unitary one in the normalized
Hilbert--Schmidt norm.

Both halves have since been proved.
`Analysis/HilbertSchmidtPolarCorrection.lean` supplies
`exists_unitary_hsNorm_sub_le`, and
`Analysis/AmenableTraceHyperlinear.lean` spends it on the group models,
choosing one index at which the Gram, multiplicative and separation defects
are simultaneously small on a finite test set, polar-correcting each model
matrix, and paying the triangle inequalities.  So the input is inhabited, and
this file inhabits it.

## What changes, and what does not

**The citation becomes a theorem.**  `brownAmenableTraceHyperlinearInput`
below is a premise-free inhabitant, so every declaration carrying
`BrownAmenableTraceHyperlinearInput` as a leading binder can now be restated
without it.  Two such restatements are given: the general implication
`isHyperlinear_of_hasFactorizationProperty'` and its instance at the literal
group.

**The input structure stays where it is.**  It is not deleted, and the primed
theorems here do not replace the unprimed ones in
`FactorizationImpliesHyperlinear.lean`.  A reader following the manuscript's
citation trail should still find the implication named, cited and isolated at
the point where it is used; what this file adds is the fact that the name is
now backed by a proof rather than by Brown's paper alone.

**Countability drops out.**  The field of the input carries `[Countable G]`,
because that is the hypothesis Brown's theorem is usually quoted under.  The
proof does not use it --- `AmenableTraceHyperlinear`'s headline has no
countability hypothesis --- so the primed forms below are stated without it,
and are genuinely stronger than what the input can deliver.

**The literal factorization property is now known.**  `ProblemX.lean` proves
`literalFactorizationProperty` from the locally-RF-by-`ℤ` structure of `E`.
The literal instance below remains useful wiring: it records that this theorem
also gives hyperlinearity by a route independent of soficity.  This adds no new
hyperlinearity information, since
`LiteralSoficAssembly.markedGroup_isHyperlinear` already supplies it.
-/

namespace GroupApproximation
namespace NinetyNineProblems

universe u

/-! ## The input, inhabited -/

/-- **Brown's Theorem 3.1.7 `(1) ⟹ (2)`, discharged.**

The content is
`AmenableTraceHyperlinear.isHyperlinear_of_isAmenableTrace_canonicalMaximal`,
which proves the implication outright; `HasFactorizationProperty G` is by
definition the amenability of the canonical trace that theorem hypothesizes,
so no translation is needed.  The `[Countable G]` binder of the field is
introduced and ignored, the proof having no use for it.

Premise-free, so `BrownAmenableTraceHyperlinearInput` is no longer an open
input of this development. -/
theorem brownAmenableTraceHyperlinearInput :
    BrownAmenableTraceHyperlinearInput.{u} :=
  ⟨fun G _ _ h ↦
    AmenableTraceHyperlinear.isHyperlinear_of_isAmenableTrace_canonicalMaximal
      G h⟩

/-! ## The consequences, restated without the binder -/

/-- **A group with the factorization property is hyperlinear**, with no
hypothesis and no countability.

This is `isHyperlinear_of_hasFactorizationProperty` of
`FactorizationImpliesHyperlinear.lean` with its leading binder removed, and
with `[Countable G]` removed as well: the proof in
`Analysis/AmenableTraceHyperlinear.lean` never uses countability, so quoting
Brown's theorem under it would understate what is proved.

Together with `not_forall_sofic_hasFactorizationProperty` of
`FactorizationProperty.lean` this pins the factorization property strictly
between residual finiteness and hyperlinearity: it implies hyperlinearity, and
Thom's examples show hyperlinearity does not imply it. -/
theorem isHyperlinear_of_hasFactorizationProperty' (G : Type u) [Group G]
    (h : HasFactorizationProperty G) : IsHyperlinear G :=
  AmenableTraceHyperlinear.isHyperlinear_of_isAmenableTrace_canonicalMaximal G h

/-- **The literal group's factorization property implies hyperlinearity** ---
unconditionally, the Brown input having been discharged.

This adds nothing about `E`.  `E` is already known to be hyperlinear, from
soficity, by `LiteralSoficAssembly.markedGroup_isHyperlinear`, and that route
is unconditional too.  The theorem is here to close the wiring.  Its premise
is now supplied by `literalFactorizationProperty`; nevertheless, the reverse
implication cannot be inferred from hyperlinearity alone, as Thom's examples
show. -/
theorem markedGroup_isHyperlinear_of_literalFactorizationProperty'
    (h : LiteralFactorizationProperty) :
    IsHyperlinear LiteralNonMFPresentation.MarkedGroup :=
  isHyperlinear_of_hasFactorizationProperty'
    LiteralNonMFPresentation.MarkedGroup (literalFactorizationProperty_iff.mp h)

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_closed_axioms brownAmenableTraceHyperlinearInput
#audit_axioms isHyperlinear_of_hasFactorizationProperty'
#audit_axioms markedGroup_isHyperlinear_of_literalFactorizationProperty'
