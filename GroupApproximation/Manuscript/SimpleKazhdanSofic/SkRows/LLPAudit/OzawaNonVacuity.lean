import GroupApproximation.Manuscript.SimpleKazhdanSofic.CStarNoLocalLifting
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.LLPAudit.UniverseLowering
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.LLPAudit.ULiftTransfer
import GroupApproximation.Meta.AxiomGuard

/-!
# Ozawa's LLP obstruction is not vacuous, and `v = 0` is its strongest form

Audit of `simple_kazhdan_sofic_group.tex`, Introduction, tex l.54–56:

> Ozawa stated the hyperlinear form in 2003, noting that the full
> $C^*$-algebra of such a group cannot have the local lifting
> property~\cite[\S7]{Ozawa}, and Pestov asked the sofic form as
> Open question~9.1~\cite{Pestov}.

The formal claim of the sentence is the closed endpoint
`SimpleKazhdanSofic.printedOzawaNoLocalLiftingGeneral`
(Manuscript/SimpleKazhdanSofic/CStarNoLocalLifting.lean:82), which negates
`LocalLifting.HasLocalLiftingProperty.{1, 0} (MaximalGroupCStar G)`.  This module audits that
negation from two sides.

* **Non-vacuity.**  The property negated there is not always false: `ℂ` has it
  (`LocalLifting.hasLocalLiftingProperty_complex`, Analysis/LocalLiftingProperty.lean:144; every
  operator system of `ℂ` is `ℂ·1` and `z ↦ z·1_B` lifts), and so does the C⋆-algebra
  `ULift.{1} ℂ` in `Type 1`, at exactly the universes `.{1, 0}` of the printed statement
  (`hasLocalLiftingProperty_ulift_complex`, via `hasLocalLiftingProperty_ulift`).
* **Universe lowering.**  The quotient universe `v` is an artefact of the formalisation.  The LLP
  at `max v w` implies the LLP at `v` (`hasLocalLiftingProperty_of_ulift`), so failure at `v = 0`
  gives failure at every `w` (`ozawaNoLocalLifting_everyUniverse`).  Thus the printed `v = 0`
  statement is the strongest of its family.

Endpoint: `manuscriptSentence_ozawaNoLocalLiftingNonVacuous`.  Names and dates in the sentence are
credit only.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit

open GroupApproximation.LocalLifting

universe w

/-- **Ozawa's obstruction at every quotient universe.**  The full C⋆-algebra of an infinite
simple hyperlinear group with property (T) fails the local lifting property with quotients in
any universe `w`; this follows from the printed `w = 0` form by universe lowering. -/
theorem ozawaNoLocalLifting_everyUniverse :
    ∀ (G : Type) [Group G] [IsSimpleGroup G] [Infinite G],
      HasKazhdanPropertyT.{0, 0} G → IsHyperlinear G →
        ¬ HasLocalLiftingProperty.{1, w} (MaximalGroupCStar G) := by
  intro G _ _ _ hT hH
  have hobs : ∀ (G : Type) [Group G] [IsSimpleGroup G] [Infinite G],
      HasKazhdanPropertyT.{0, 0} G → IsHyperlinear G →
        ¬ HasLocalLiftingProperty.{1, 0} (MaximalGroupCStar G) :=
    printedOzawaNoLocalLiftingGeneral
  exact not_hasLocalLiftingProperty_max_of_not.{1, 0, w} (hobs G hT hH)

/-- **tex l.54–56, audit endpoint.**
(1) `ℂ` has the local lifting property.
(2) Some C⋆-algebra in `Type 1` has the local lifting property with quotients in `Type 0`, so
the property negated by `printedOzawaNoLocalLiftingGeneral` is not always false.
(3) The printed obstruction holds with quotients in every universe `w`. -/
theorem manuscriptSentence_ozawaNoLocalLiftingNonVacuous :
    HasLocalLiftingProperty.{0, 0} ℂ ∧
      (∃ (A : Type 1) (_ : CStarAlgebra A), HasLocalLiftingProperty.{1, 0} A) ∧
      ∀ (G : Type) [Group G] [IsSimpleGroup G] [Infinite G],
        HasKazhdanPropertyT.{0, 0} G → IsHyperlinear G →
          ¬ HasLocalLiftingProperty.{1, w} (MaximalGroupCStar G) :=
  ⟨hasLocalLiftingProperty_complex,
    ⟨ULift.{1} ℂ, inferInstance, hasLocalLiftingProperty_ulift_complex⟩,
    ozawaNoLocalLifting_everyUniverse⟩

end GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.ozawaNoLocalLifting_everyUniverse
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.manuscriptSentence_ozawaNoLocalLiftingNonVacuous
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.LLPAudit.manuscriptSentence_ozawaNoLocalLiftingNonVacuous
