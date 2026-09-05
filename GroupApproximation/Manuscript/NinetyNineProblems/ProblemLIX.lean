import GroupApproximation.Analysis.LIXEndpointStatement
import GroupApproximation.Analysis.CStarSimple
import GroupApproximation.Meta.AxiomGuard

/-!
# STW Problem LIX

Schafhauser, Tikuisis and White, *Nuclear C⋆-algebras: 99 problems*,
arXiv:2506.10902, print as Problem LIX, verbatim:

> Are all unital simple C*-algebras K1-injective?

`ProblemLIX` below is that question.

STW record it as open, and the surrounding discussion fixes what a
counterexample has to avoid: Rieffel's Theorem 2.10 gives `K₁`-injectivity at
stable rank one and Lin's gives it at real rank zero, so a counterexample has
neither.  Villadsen's examples already defeat the *surjectivity* analogue in
the simple separable nuclear class; injectivity is the direction STW call open.

## What the statement says, clause by clause

* **unital** --- Mathlib's `CStarAlgebra` extends `NormedRing`, which is
  unital, so the word carries no separate hypothesis
  (`Mathlib/Analysis/CStarAlgebra/Classes.lean:38`).
* **nontrivial** --- asked separately rather than folded into simplicity,
  because the convention that a simple algebra is nonzero is a convention.
  The hypothesis is not free: it weakens `ProblemLIX`, so the negation is
  correspondingly *stronger*, and a counterexample has to be exhibited as a
  nonzero algebra rather than sliding in on the zero one.  It also could not
  have been the zero algebra: there the unitary group is a singleton, so
  `U(A)/U₀(A)` is trivial and every map out of it is injective.
* **simple** --- `IsSimpleCStar A`, every closed two-sided ideal is `⊥` or
  `⊤` (`Analysis/CStarSimple`).  Not Mathlib's `IsSimpleRing`, which asks the
  same of *algebraic* two-sided ideals.  The two agree for a unital
  C⋆-algebra, because a proper two-sided ideal of a unital Banach algebra
  contains no unit and `nonunits` is closed, so the closure stays proper ---
  but that agreement is landed as `isSimpleCStar_iff_isSimpleRing` rather than
  assumed, and the endpoint says what the problem says.
* **`K₁`-injective** --- `K1Inj A`, injectivity of the canonical
  `U(A)/U₀(A) → K₁(A)`.  `U₀(A)` is the path component of `1` in the unitary
  group (`unitaryComponentOne`, built on Mathlib's `Subgroup.pathComponentOne`),
  and `K₁(A)` is the colimit of `U(Mₙ(A))/U₀(Mₙ(A))` along `u ↦ diag (u, 1)`
  (`Analysis/CStarKOne`).  Both are generic: no declaration in that chain
  mentions any particular algebra, and all three modules under `CStarKOne`
  --- `SequentialGroupColimit`, `CStarUnitaryComponent` and
  `CStarMatrixBlockInclusion` --- import Mathlib and nothing else.

## Two recorded choices

**The universe.**  `KOne` is universe-polymorphic, so quantifying `ProblemLIX`
over `Type` is genuinely *weaker* than quantifying over `Type u`, and a weaker
universal is a stronger negation --- the direction in which a free choice can
flatter the result.  `Type` is chosen anyway, and on the merits: the algebra a
counterexample produces is a concrete separable one built from matrices over
`C(X, ℂ)`, so it lives in `Type 0`, and `Type 0` is what the printed problem
means.  Recorded so that it reads as a decision and not as an artefact of
whichever line was typed first.

**The order instances.**  Mathlib's C⋆-structure on `Mₙ(A)` asks for
`[PartialOrder A]` and `[StarOrderedRing A]` on top of `[CStarAlgebra A]`, so
`K1Injective` --- and anything mentioning `CStarMat n A` --- carries those two
instance arguments.  Quantifying over them here would look like quantifying
over a choice of order.  It is not one: `StarOrderedRing` characterises `x ≤ y`
by `y - x` lying in the additive closure of `{star s * s}`
(`Mathlib/Algebra/Order/Star/Basic.lean:79`), so any two such orders on a
starred ring coincide.  Rather than argue that, the endpoint is stated over
`K1Inj`, which is `K1Injective` with `CStarAlgebra.spectralOrder` supplied in
its body (`Analysis/LIXEndpointStatement`), leaving no order quantification to
justify.

## What is here and what is not

The statement lands before anything is proved about it, which is the point: an
endpoint written after the proof, in the proof's vocabulary, cannot be audited
from outside.  `not_problemLIX_of_exists` is the whole of the logic between the
counterexample and the printed problem, and it takes the counterexample as a
hypothesis.

The counterexample itself is not here yet.  Nothing in this file asserts that
`ProblemLIX` is false, and `not_problemLIX_of_exists` is audited with
`#audit_axioms`, not `#audit_closed_axioms`, precisely because it has a leading
input.
-/

namespace GroupApproximation
namespace NinetyNineProblems

/-- **STW Problem LIX**: are all unital simple C⋆-algebras `K₁`-injective?

`CStarAlgebra` is unital, `IsSimpleCStar` is simplicity for closed two-sided
ideals, and `K1Inj` is injectivity of the canonical `U(A)/U₀(A) → K₁(A)` with
the spectral order pinned.  Quantified over `Type`, deliberately; see the
module docstring for that choice and for the clause-by-clause reading. -/
def ProblemLIX : Prop :=
  ∀ (A : Type) [CStarAlgebra A], Nontrivial A → IsSimpleCStar A → K1Inj A

/-- **A counterexample refutes the printed problem**, and no excluded middle is
used to get from one to the other.

Stated as an implication rather than folded into the refutation because the
existential is the stronger statement: `¬ ProblemLIX` follows from it, and not
conversely.  A negated universal does not exhibit anything. -/
theorem not_problemLIX_of_exists
    (h : ∃ (A : Type) (_inst : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleCStar A ∧ ¬ K1Inj A) :
    ¬ ProblemLIX := by
  obtain ⟨A, _inst, hnt, hsimp, hnk⟩ := h
  exact fun hLIX => hnk (hLIX A hnt hsimp)

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_axioms ProblemLIX
#audit_axioms not_problemLIX_of_exists
