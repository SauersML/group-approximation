import GroupApproximation.Analysis.PropertyAExtension
import GroupApproximation.Sofic.LiteralNonMFLinearWitness

/-!
# The exactness paragraph, with its trust boundary made explicit

`Analysis/ExactnessPermanence.lean` splits the manuscript's exactness chain for
the Clifford witness `W = ClLamp(X) ⋊ V` into four links `E.1`--`E.4` and
grades each one.  Two of the four are closed at group level:

* `E.1` — the lamp kernel is locally finite, hence amenable, hence has
  property A (`ExactnessPermanence.hasPropertyA_cliffordLamp_viaAmenability`);
* `E.3` — property A passes to extensions, in the semidirect form the
  manuscript uses
  (`ExactnessPermanence.hasPropertyA_semidirectProduct_of_isLocallyFiniteGroup`).

`E.2` is Guentner--Higson--Weinberger for a linear group, and `E.4` is the
Kirchberg--Wassermann crossover from group exactness to `C*`-algebra
exactness.  Neither is available: `E.2` runs through affine buildings over
completions of a finitely generated field, and `E.4` cannot even be *stated*
until Mathlib has a `C*`-norm on a tensor product.

That grading is spread over a table, a status list and an engineering
assessment, and a reader has to assemble it to see what is actually assumed.
This file assembles it, in one theorem per object.

## What the theorem says

`ambient_hasPropertyA_of_vertical` takes **one** hypothesis — property A for
the vertical (linear) group — and returns property A for the whole ambient
group.  Everything else in the group half of the paragraph is discharged
inside the proof.  So the remaining trust surface of the group side is exactly
the cited `GHW`, with nothing else hidden behind it, and the remaining trust
surface of the paragraph as a whole is exactly `GHW` together with the
Kirchberg--Wassermann crossover.

## What the theorem does not say

It does not say that `W` is exact, that `Cred(W)` is exact, or that property A
implies exactness.  Property A *is* group exactness for a countable discrete
group by Higson--Roe and Ozawa, and that equivalence is not formalized here
either; the conclusion is the combinatorial statement and nothing more.  The
manuscript's own sentence — "All parts of this paragraph except exactness are
also verified in Lean; the present formal library has no definition of exact
`C*`-algebras" — remains accurate, and this file is a statement about which
*parts* those are.

No `\leanverified` badge is owed for a conditional theorem; the module exists
so that the conditionality inventory can point at one hypothesis instead of at
a prose grading table.
-/

namespace GroupApproximation
namespace ExactnessGroupSideEndpoint

open ExactnessPermanence
open MarkedCompression

universe u

/-- **The group side of the exactness paragraph, on one hypothesis.**

Given property A for the vertical group — the manuscript's `E.2`, cited to
Guentner--Higson--Weinberger for the linear group `V ≤ GL₄(ℚ)` — the ambient
marked-compression group `ClLamp(Cosets) ⋊ V` has property A.

The two links consumed inside are the ones the repository owns: the lamp
kernel is locally finite (`E.1`), and property A passes to semidirect products
(`E.3`).  Neither appears as a hypothesis, so the hypothesis list *is* the
trust surface. -/
theorem ambient_hasPropertyA_of_vertical {Γ : Type u} [Group Γ]
    (α : Γ →* Γ) (hα : Function.Injective α)
    (hV : HasPropertyA (Vertical α hα)) :
    HasPropertyA (Ambient α hα) :=
  hasPropertyA_semidirectProduct_of_isLocallyFiniteGroup
    (CliffordLamp.isLocallyFiniteGroup_cliffordLamp (Cosets α hα)) hV

/-- The same statement at the manuscript's own witness group. -/
theorem witnessGroup_hasPropertyA_of_vertical
    (hV : HasPropertyA
      (Vertical LiteralNonMFLinearWitness.alpha
        ExplicitLinearModel.conjD_injective)) :
    HasPropertyA LiteralNonMFLinearWitness.WitnessGroup :=
  ambient_hasPropertyA_of_vertical _ _ hV

end ExactnessGroupSideEndpoint
end GroupApproximation
