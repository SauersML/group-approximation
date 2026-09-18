import GroupApproximation.Analysis.QuasidiagonalTrace
import GroupApproximation.Analysis.ReducedGroupCStarStablyFinite
import GroupApproximation.Analysis.TikuisisWhiteWinterProof
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work (Tikuisis--White--Winter): the definitions

Census row `82cac0c03a39`, `non_mf_groups_exist.tex` L315--318 (Related work,
paragraph starting at L310):

> It also asked whether every separable nuclear stably finite $C^*$-algebra is
> quasidiagonal; for algebras that satisfy the universal coefficient theorem
> and have a faithful trace, the theorem of Tikuisis, White, and Winter recalled
> above answers this~\cite{TWW}.

The theorem "recalled above" is at L279--281:

> Tikuisis, White, and Winter proved that faithful traces on separable nuclear
> $C^*$-algebras satisfying the universal coefficient theorem are
> quasidiagonal~\cite{TWW}

This module fixes the vocabulary of the sentence.

* `QuasidiagonalModel` and `IsQuasidiagonalCStarAlgebra` define quasidiagonality
  of a separable unital C⋆-algebra in Voiculescu's abstract form: completely
  positive contractions `φₙ : A → M_{kₙ}` that are asymptotically multiplicative
  in operator norm and recover every norm as `limsup ‖φₙ a‖ = ‖a‖`. Equivalently,
  there is a faithful embedding `A ↪ ∏ M_{kₙ} / ⊕ M_{kₙ}` with a completely
  positive contractive lift, because the corona norm is the limsup of the
  coordinate norms. For separable `A` this is equivalent to the
  operator-theoretic definition (a faithful representation that is a
  quasidiagonal set of operators), by Voiculescu's theorem (see Brown--Ozawa,
  Chapter 7). The passage from `limsup` to `lim` uses finite direct sums of
  consecutive models.
* `IsStablyFiniteCStarAlgebra` (already in the corpus) is stable finiteness:
  every isometry in every matrix amplification is a unitary.
* `BlackadarKirchbergQuasidiagonalQuestion` is the printed question.
* `TikuisisWhiteWinterStatement T` is the recalled theorem of L279--281, with the
  UCT read as `T.SatisfiesUCT`: `KK`-equivalence to a commutative separable
  C⋆-algebra in the Kasparov theory `T`. That is Rosenberg--Schochet's
  characterization of the bootstrap class. It is not vacuous: it is exactly the
  UCT once `T` is Kasparov's `KK`. It is equivalent to the corpus's
  `QuasidiagonalMF.TikuisisWhiteWinterTheorem T` (`tikuisisWhiteWinterStatement_iff`).
* `BlackadarKirchbergQuasidiagonalAnswerUCTFaithfulTrace T` is the question
  restricted to UCT algebras with a faithful tracial state. That restriction is
  "answers this".

## Proof route of the row

The elementary content is in `RelatedTWW.Elementary`:
quasidiagonal ⇒ MF ⇒ stably finite, and a faithful quasidiagonal trace ⇒ a
quasidiagonal algebra. That a faithful trace forces stable finiteness is the
corpus theorem `NinetyNineProblems.isStablyFiniteCStarAlgebra_of_faithfulTracialState`. The last is Brown's
argument: the corona map of the trace models is injective because its kernel is
killed by the faithful trace.

`RelatedTWW.Sentence` assembles the printed sentence. Given
`TikuisisWhiteWinterStatement T` it proves the restricted answer.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace RelatedTWW

open Filter
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

/-! ## Quasidiagonal C⋆-algebras -/

/-- **Quasidiagonal matrix models** of a unital C⋆-algebra `A`: completely
positive contractions `φₙ : A → M_{kₙ}` that respect the adjoint, are
asymptotically multiplicative in operator norm, and recover every norm as a
limsup.

The `map_star` clause is automatic for completely positive maps. It is kept
so that the non-unital contractions need no separate self-adjointness argument.
Contractions rather than unital maps are used so that the models of the zero
algebra are allowed. -/
structure QuasidiagonalModel (A : Type u) [CStarAlgebra A] where
  /-- The finite matrix sizes `kₙ`. -/
  space : ℕ → FiniteModel
  /-- Each matrix size is positive. -/
  nonempty : ∀ n : ℕ, Nonempty (space n)
  /-- The maps `φₙ : A → M_{kₙ}`, genuinely `ℂ`-linear. -/
  map : ∀ n : ℕ, A →ₗ[ℂ] Matrix (space n) (space n) ℂ
  /-- Each `φₙ` is completely positive. -/
  completelyPositive : ∀ n : ℕ,
    Quasidiagonal.IsCompletelyPositiveOnMatrices (space n) ⇑(map n)
  /-- Each `φₙ` is a contraction. -/
  norm_le : ∀ (n : ℕ) (a : A), ‖map n a‖ ≤ ‖a‖
  /-- Each `φₙ` respects the adjoint. -/
  map_star : ∀ (n : ℕ) (a : A), map n (star a) = Matrix.conjTranspose (map n a)
  /-- Asymptotic multiplicativity in operator norm. -/
  tendsto_mul : ∀ a b : A,
    Tendsto (fun n ↦ ‖map n (a * b) - map n a * map n b‖) atTop (nhds 0)
  /-- Norm recovery: the corona norm of the image of `a` is `‖a‖`. -/
  limsup_norm : ∀ a : A, Filter.limsup (fun n ↦ ‖map n a‖) atTop = ‖a‖

/-- **Quasidiagonality of a C⋆-algebra**: `A` is separable and has
quasidiagonal matrix models. By Voiculescu's theorem this is the usual
definition for separable algebras. -/
def IsQuasidiagonalCStarAlgebra (A : Type u) [CStarAlgebra A] : Prop :=
  TopologicalSpace.SeparableSpace A ∧ Nonempty (QuasidiagonalModel A)

/-! ## The printed question -/

/-- **The Blackadar--Kirchberg question** of L315--316: every separable nuclear
stably finite C⋆-algebra is quasidiagonal. It is recorded as a proposition and
is not asserted anywhere. -/
def BlackadarKirchbergQuasidiagonalQuestion : Prop :=
  ∀ (A : Type u) [CStarAlgebra A], TopologicalSpace.SeparableSpace A →
    CStarExactness.IsNuclearCStarAlgebra A → IsStablyFiniteCStarAlgebra A →
      IsQuasidiagonalCStarAlgebra A

/-- **The question on the class of L317**, the separable nuclear stably finite
algebras that satisfy the UCT (at the Kasparov theory `T`) and have a faithful
tracial state. The printed sentence says the theorem of Tikuisis, White, and
Winter answers the question here, positively. -/
def BlackadarKirchbergQuasidiagonalAnswerUCTFaithfulTrace
    (T : KK.KasparovTheory.{u}) : Prop :=
  ∀ S : KK.SepCStarAlgebra.{u}, CStarExactness.IsNuclearCStarAlgebra S →
    IsStablyFiniteCStarAlgebra S → T.SatisfiesUCT S →
      Nonempty (FaithfulTracialState S) → IsQuasidiagonalCStarAlgebra S

/-! ## The recalled theorem, as the one named gap -/

/-- **The theorem of Tikuisis, White, and Winter** (L279--281): every faithful
tracial state on a separable nuclear C⋆-algebra satisfying the UCT is
quasidiagonal.

Separability is carried by `KK.SepCStarAlgebra`. The UCT is `T.SatisfiesUCT`,
`KK`-equivalence to a commutative algebra in the Kasparov theory `T`; see the
module docstring. Quasidiagonality of the trace is the corpus's
`Quasidiagonal.IsQuasidiagonalTrace`: unital completely positive, asymptotically
multiplicative matrix models whose normalized traces converge to `τ`.

This is the single unproved input of the row. The Annals proof (with its
Kasparov-theory prerequisites) is out of reach of this development. -/
def TikuisisWhiteWinterStatement (T : KK.KasparovTheory.{u}) : Prop :=
  ∀ S : KK.SepCStarAlgebra.{u}, CStarExactness.IsNuclearCStarAlgebra S →
    T.SatisfiesUCT S → ∀ τ : FaithfulTracialState S,
      Quasidiagonal.IsQuasidiagonalTrace (fun a : S ↦ τ a)

/-- The named gap is the corpus's `QuasidiagonalMF.TikuisisWhiteWinterTheorem`,
unbundled. -/
theorem tikuisisWhiteWinterStatement_iff (T : KK.KasparovTheory.{u}) :
    TikuisisWhiteWinterStatement T ↔
      QuasidiagonalMF.TikuisisWhiteWinterTheorem T :=
  ⟨fun h ↦ ⟨h⟩, fun h ↦ h.quasidiagonal⟩

/-- **The question implies its restricted answer.** The restriction to UCT
algebras with a faithful trace is a special case of the question, so answering
it there is a genuine partial answer. -/
theorem blackadarKirchbergQuasidiagonalAnswerUCTFaithfulTrace_of_question
    (hq : BlackadarKirchbergQuasidiagonalQuestion.{u})
    (T : KK.KasparovTheory.{u}) :
    BlackadarKirchbergQuasidiagonalAnswerUCTFaithfulTrace T := by
  intro S hnuc hsf _ _
  exact hq S inferInstance hnuc hsf

end

end RelatedTWW
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedTWW.QuasidiagonalModel
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedTWW.IsQuasidiagonalCStarAlgebra
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedTWW.BlackadarKirchbergQuasidiagonalQuestion
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedTWW.BlackadarKirchbergQuasidiagonalAnswerUCTFaithfulTrace
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedTWW.TikuisisWhiteWinterStatement
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedTWW.tikuisisWhiteWinterStatement_iff
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedTWW.blackadarKirchbergQuasidiagonalAnswerUCTFaithfulTrace_of_question
