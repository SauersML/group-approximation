import GroupApproximation.Analysis.LIXEndpointStatement
import GroupApproximation.Analysis.CStarSimple
import GroupApproximation.Analysis.LIXLimitSimple
import GroupApproximation.Analysis.LIXLemmaTwoProp
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
from outside.  Three steps follow it and every one takes the counterexample as
input:

* `exists_simple_unital_not_k1Inj_of` — the existential from *any* algebra with
  the three properties;
* `exists_simple_unital_not_k1Inj_of_limit` — the same at the actual algebra
  `LIX.LIXLimit`, so the only inputs left are its simplicity and its witness;
* `not_problemLIX_of_exists` — the existential to the negation of the printed
  universal.

Between them there is no mathematics, only applications.

That the construction is *imported* here does not weaken the statement.  The
requirement is that `ProblemLIX` be written in generic vocabulary, and it is:
its definitional closure is `CStarAlgebra`, `Nontrivial`, `IsSimpleCStar` and
`K1Inj`, none of which mentions the tower, and `K1Inj`'s own module imports
only the six generic ones.  What an endpoint may not do is be *stated* in the
proof's vocabulary, and this one is not.

**The counterexample itself is not proved yet.**  Nothing in this file asserts
that `ProblemLIX` is false, and every theorem here is audited with
`#audit_axioms`, not `#audit_closed_axioms`, precisely because each has a
leading input.  What is still owed, by two other lanes, is simplicity of
`LIX.LIXLimit` (stage-wise fullness) and its witness (the generalized
Corollary 4 with Lemma 6, and the null-homotopy of `diag (u, 1)`).  When those
arrive, `exists_simple_unital_not_k1Inj` and `not_problemLIX` are two closed
statements and two `#audit_closed_axioms` lines.
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

/-- **The counterexample assembly.**  One nontrivial simple C⋆-algebra carrying
a single unitary that is not null-homotopic but whose `diag (·, 1)` is
discharges the existential.

`HasK1InjWitness` is `Analysis/LIXEndpointStatement`'s name for that unitary's
existence, and `not_k1Inj_of_hasWitness` is the only step of `K₁`-theory the
refutation uses.  Nothing about `K₁(A)` is computed: not that it vanishes, not
that `U(A)/U₀(A)` has order two.  Both would need further theorems, and neither
is part of the answer to Problem LIX.

Every argument is data about a specific algebra, so this is audited with
`#audit_axioms`.  It is the assembly, not the answer. -/
theorem exists_simple_unital_not_k1Inj_of
    (A : Type) [CStarAlgebra A] (hnt : Nontrivial A) (hsimp : IsSimpleCStar A)
    (hw : HasK1InjWitness A) :
    ∃ (B : Type) (_inst : CStarAlgebra B),
      Nontrivial B ∧ IsSimpleCStar B ∧ ¬ K1Inj B :=
  ⟨A, inferInstance, hnt, hsimp, not_k1Inj_of_hasWitness hw⟩

/-- **The assembly at the counterexample algebra**, modulo the two facts about
it that the construction still owes.

`LIX.LIXLimit` is the inductive limit of the STW LIX tower
(`Analysis/LIXLimitAlgebra`), and its `CStarAlgebra` and `Nontrivial` instances
are found by `inferInstance` — the first through the completion, the second
from nontriviality of stage zero.  So the only inputs are the two named
propositions, both of which are stated in this file's own generic vocabulary
and neither of which mentions an order.

That is not an accident of presentation.  `IsSimpleCStar` takes `[CStarAlgebra A]`
alone, and `HasK1InjWitness` keeps the spectral order inside its body rather
than in its statement, which is why the concrete algebra can be plugged in here
without either lane and this file having to agree on which `PartialOrder` term
they wrote. -/
theorem exists_simple_unital_not_k1Inj_of_limit
    (hsimp : IsSimpleCStar LIX.LIXLimit) (hwit : HasK1InjWitness LIX.LIXLimit) :
    ∃ (A : Type) (_inst : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleCStar A ∧ ¬ K1Inj A :=
  exists_simple_unital_not_k1Inj_of LIX.LIXLimit inferInstance hsimp hwit

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

/-! ## Against the single topological input -/

/-- **The endpoint reduced to Lemma 2**, with the two facts about the
counterexample algebra still explicit.

`LIX.LemmaTwoHolds` (`Analysis/LIXLemmaTwoProp`) is the only thing the whole
argument takes from algebraic topology: at every stage of the tower, `F ⊕ H`
and `𝟏² ⊕ H` are not Murray--von Neumann equivalent as continuous fields.
Everything else --- the stage algebras, the connecting maps, the limit, its
simplicity, and the reduction of `¬ ProblemLIX` to one unitary --- is
unconditional.

Simplicity is no longer a hypothesis anywhere: `LIX.lixLimit_isSimpleCStar`
proves `IsSimpleCStar LIX.LIXLimit` outright, from `cs-stages`' stagewise
fullness through `cs-limit`'s reduction, with no argument.

**One argument remains in the entire chain**, `cs-clutching`'s
`lixLimit_hasK1InjWitness_of : LemmaTwoHolds → HasK1InjWitness LIX.LIXLimit`.
It is a hypothesis here only so that this file stays green while it lands; the
`_of_lemmaTwo` forms replace it by that name when it arrives, and nothing about
the statements changes when they do. -/
theorem exists_simple_unital_not_k1Inj_of_lemmaTwo_data
    (hwit : LIX.LemmaTwoHolds → HasK1InjWitness LIX.LIXLimit)
    (h : LIX.LemmaTwoHolds) :
    ∃ (A : Type) (_inst : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleCStar A ∧ ¬ K1Inj A :=
  exists_simple_unital_not_k1Inj_of_limit LIX.lixLimit_isSimpleCStar (hwit h)

/-- **Lemma 2 refutes Problem LIX**, with the same two facts still explicit.

When the two hypotheses are discharged this becomes
`not_problemLIX_of_lemmaTwo : LIX.LemmaTwoHolds → ¬ ProblemLIX`, and the
endpoint's entire dependency on algebraic topology is that one arrow. -/
theorem not_problemLIX_of_lemmaTwo_data
    (hwit : LIX.LemmaTwoHolds → HasK1InjWitness LIX.LIXLimit)
    (h : LIX.LemmaTwoHolds) : ¬ ProblemLIX :=
  not_problemLIX_of_exists (exists_simple_unital_not_k1Inj_of_lemmaTwo_data hwit h)

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_axioms ProblemLIX
#audit_axioms exists_simple_unital_not_k1Inj_of
#audit_axioms exists_simple_unital_not_k1Inj_of_limit
#audit_axioms exists_simple_unital_not_k1Inj_of_lemmaTwo_data
#audit_axioms not_problemLIX_of_lemmaTwo_data
#audit_axioms not_problemLIX_of_exists
