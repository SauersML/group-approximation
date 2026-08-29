import GroupApproximation.Sofic.WeakMFUltraproduct

/-!
# The universal-ultraproduct residual and the marked-compression endpoint

This file isolates the exact formal endpoint of the marked Kazhdan-compression
obstruction.  An element is `NormMFInvisible` when every homomorphism from its
group to every operator-norm matrix ultraproduct kills it.  The quantifier is
over every ultrafilter, including principal ultrafilters.  Such elements form
the universal-ultraproduct residual defined below.  This is not definitionally
the paper's cofinite-corona radical.  For countable groups,
`NormMFCoronaRadical` proves elementwise equivalence and equality of the two
subgroups.  A single nonidentity element in this residual precludes
weak/operator-norm MF approximation.

The final section records the group word used by the explicit construction:

`w = [t c t⁻¹, a (t c t⁻¹) a⁻¹]`.

This module supplies the residual/detector layer: it turns a proof that the
marked word is `NormMFInvisible`, together with `w ≠ 1`, into `¬ IsWeakMF G`
using the repository's faithful-ultraproduct theorem.  The analytic
invisibility theorem is proved downstream, without an added premise, in
`MarkedCompressionSequentialKill`; the concrete public assembly is
`ChosenNonMFTheorem`.

No C*-algebraic premise is hidden in the definitions below: the targets are
literally `UniversalWeakMF`, the operator-norm matrix ultraproduct already
constructed in `WeakMFUltraproduct`.
-/

namespace GroupApproximation

open Filter
open scoped commutatorElement

universe u
universe v

variable {G : Type u} [Group G]

/-! ## The universal operator-norm-ultraproduct residual -/

/-- An element is invisible to operator-norm matrix ultraproducts when every
homomorphism into every such ultraproduct kills it.  This includes targets
built from principal ultrafilters; use `CoronaMFInvisible` for the paper's
cofinite-corona formulation. -/
def NormMFInvisible (x : G) : Prop :=
  ∀ (I : Type) (U : Ultrafilter I) (X : I → FiniteModel)
    (rho : G →* UniversalWeakMF U X), rho x = 1

/-! ## The marked compression word -/

/-- The marked commutator converting strict compression of a Kazhdan fixed
space into a group element:

`[t c t⁻¹, a (t c t⁻¹) a⁻¹]`.
-/
def markedCompressionWord (t a c : G) : G :=
  ⁅t * c * t⁻¹, a * (t * c * t⁻¹) * a⁻¹⁆

end GroupApproximation
