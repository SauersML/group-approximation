import GroupApproximation.Manuscript.NonMF.DGO235UniqueTraceFromAveraging
import GroupApproximation.Analysis.PowersAveragingFromPowersProperty

/-!
# Dahmani--Guirardel--Osin, Theorem 2.35, on one combinatorial hypothesis

`Manuscript/NonMF/DGO235UniqueTraceFromAveraging` reduced the printed citation
to the Powers *averaging estimate*.  `Analysis/PowersAveragingFromPowersProperty`
proves that estimate from Powers' *combinatorial* condition.  Composing the two
leaves the citation resting on

> for every finite `F ⊆ G` avoiding `1` and every `n > 0`, a partition
> `G = C ⊔ D` with `f C ∩ C = ∅` for `f ∈ F` and `n` elements whose translates
> of `D` are pairwise disjoint,

which mentions no Hilbert space, no norm, and no algebra.

## Two residuals, and which is minimal

They are different and should not be confused.

* `PowersAveragingAtHypEmbedded` is the **minimal** residual — the averaging
  estimate itself.  Haagerup's theorem makes the averaging property *equivalent*
  to C⋆-simplicity, so this Prop is exactly what DGO's Theorem 2.35 asserts,
  restated quantitatively.
* `PowersPropertyAtAcylindricallyHyperbolic` below is **strictly stronger**, and
  that is not a hedge: a Powers group is C⋆-simple with a unique trace, but the
  converse fails, and de la Harpe and Préaux name a counterexample — *"there are
  C⋆-simple groups which are not Powers groups (for example any direct product
  of non-abelian free groups)"* (arXiv:0909.3528, Item 8(vii)).  So this Prop is
  **not** what Dahmani--Guirardel--Osin's Theorem 2.35 asserts, and their own
  proof does not establish it: it produces a free normal subgroup and applies
  Akemann--Lee, which yields C⋆-simplicity, not Powers' property.

**Use `Manuscript/NonMF/DGO235PowersRoute` for the live chain**, not this
module.  There the Akemann--Lee step is carried at the averaging estimate, where
it is a true statement, and the only combinatorial input is Powers' property for
*free* groups — which is a theorem, Item 8(iv) of the same paper: *"torsion-free
Gromov-hyperbolic groups are Powers groups; in particular, non-abelian free
groups are Powers groups."*  This module is kept because the implication it
proves is correct and because a future proof that acylindrically hyperbolic
groups with trivial finite radical are Powers groups would close the corollary
through it.

## Manuscript status

Reduction step for `cor:regular-nonmf-algebra`; certifies no printed sentence on
its own.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.ReducedGroupCStarTrace

/-- **Powers' combinatorial condition at the hypotheses of
`cor:regular-nonmf-algebra`.** -/
def PowersPropertyAtAcylindricallyHyperbolic : Prop :=
  ∀ (G : Type) [Group G] [Countable G] [IsAcylindricallyHyperbolic G],
    HasTrivialFiniteRadical G → PowersProperty G

/-- **The averaging form follows from the combinatorial form.** -/
theorem powersAveragingAtAcylindricallyHyperbolic_of_powersProperty
    (h : PowersPropertyAtAcylindricallyHyperbolic) :
    PowersAveragingAtAcylindricallyHyperbolic := by
  intro G instG instC instAH hrad
  letI := instG
  letI := instC
  letI := instAH
  exact powersAveragingEstimate_of_powersProperty G (h G hrad)

/-- **`DGOTheorem235Printed` rests on Powers' combinatorial condition alone.**

Every analytic step between the two is a theorem of this repository: the
coordinate projections of `ℓ²(G)`, the `√n` gain from almost-orthogonality, the
partition estimate, the density of finite combinations of translations, and the
passage from the estimate to simplicity and to uniqueness of the trace. -/
theorem dgoTheorem235Printed_of_powersProperty
    (h : PowersPropertyAtAcylindricallyHyperbolic) : DGOTheorem235Printed :=
  dgoTheorem235Printed_of_powersAveraging_acylHyperbolic
    (powersAveragingAtAcylindricallyHyperbolic_of_powersProperty h)

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

#audit_axioms powersAveragingAtAcylindricallyHyperbolic_of_powersProperty
#audit_axioms dgoTheorem235Printed_of_powersProperty
