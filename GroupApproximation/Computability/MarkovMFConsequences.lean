import GroupApproximation.Computability.PresentationCodes
import Mathlib.Computability.RE

/-!
# Conditional Markov consequences for MF recognition

This file isolates the computability-theoretic consequence of an
Adian--Rabin construction from the construction itself.  In particular, no
Adian--Rabin theorem is asserted as an axiom.  A user of this file must supply
an explicit computable transformation of presentation codes together with
its correctness equivalence.

The vocabulary those consequences are phrased in --- `MarkovWitness`,
`FinitePresentationSemantics`, `operatorMFProperty`, `AdianRabinReduction` and
the two pullback lemmas --- lives one file upstream, in
`Computability.MarkovReductionInterface`, under this same namespace.  The
reason is the coding: the manuscript's undecidability corollary is printed *in
the recursive coding of finite presentations*, and the paragraph following it
says why an arbitrary semantics would not do --- a semantics need only attach a
finitely presented group to each code, not do so effectively, and an ineffective
choice would make the statement true for reasons having nothing to do with
groups.  So the consequence drawn here is drawn at `PresentationCodes.semantics`,
which forces this file to sit downstream of the coding.

What stays generic is the *source* problem, exactly as the manuscript says: the
reduction interface asks for a computable map and a correctness equivalence, and
does not require its source to be a word problem.
-/

namespace GroupApproximation
namespace MarkovMFConsequences

universe u v

/-- **Specialized undecidability statement for operator-MF recognition**, at the
recursive coding and under an explicitly supplied Adian--Rabin reduction from an
undecidable source problem.

The source problem is arbitrary --- that is the point of the interface, and what
lets `Computability.HaltingReduction` reduce from the halting problem rather
than from a word problem.  The coding is not arbitrary: it is
`PresentationCodes.semantics`, where the group is read syntactically off the
code, so the conclusion is about deciding MF-ness from a presentation and cannot
be met by an ineffective choice of semantics. -/
theorem operatorMF_recognition_undecidable :
    ∀ {Source : Type u} [Primcodable Source]
      {sourceProperty : Source → Prop}
      (_reduction : AdianRabinReduction sourceProperty
        (operatorMFProperty PresentationCodes.semantics))
      (_source_undecidable : ¬ComputablePred sourceProperty),
      ¬ComputablePred (operatorMFProperty PresentationCodes.semantics) := by
  intro Source _ sourceProperty reduction source_undecidable
  exact recognition_undecidable reduction source_undecidable

/-- Specialized non-r.e. statement for negative operator-MF instances. -/
theorem operatorMF_negative_side_not_re
    {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
    {sourceProperty : Source → Prop}
    (semantics : FinitePresentationSemantics Code)
    (reduction : AdianRabinReduction sourceProperty
      (operatorMFProperty semantics))
    (source_negative_not_re : ¬REPred (fun source ↦ ¬sourceProperty source)) :
    ¬REPred (fun code ↦ ¬operatorMFProperty semantics code) :=
  negative_side_not_re reduction source_negative_not_re

/-- Closed form of the non-r.e. statement: every binder after the colon, so the
manuscript can cite it as a complete printed proposition.  Its hypotheses --- a
presentation coding, an Adian--Rabin reduction, and a source whose negative side
is not recursively enumerable --- are visible antecedents, not citations. -/
theorem manuscriptOperatorMFNegativeSideNotRE :
    ∀ {Source : Type u} {Code : Type v} [Primcodable Source] [Primcodable Code]
      {sourceProperty : Source → Prop}
      (semantics : FinitePresentationSemantics Code)
      (_reduction : AdianRabinReduction sourceProperty
        (operatorMFProperty semantics))
      (_source_negative_not_re :
        ¬REPred (fun source ↦ ¬sourceProperty source)),
      ¬REPred (fun code ↦ ¬operatorMFProperty semantics code) := by
  intro Source Code _ _ sourceProperty semantics reduction hnre
  exact operatorMF_negative_side_not_re semantics reduction hnre

/-! The two group-theoretic inputs normally used to build the MF Markov
witness are already unconditional theorems in this repository.  They are
recorded here without claiming that the syntactic Adian--Rabin transformation
has been formalized. -/

/-- Operator-MF is inherited by subgroups. -/
theorem operatorMF_subgroup_hereditary :
    ∀ {G : Type u} [Group G] (_hG : IsOperatorMF G) (H : Subgroup G),
      IsOperatorMF H := by
  intro G _ hG H
  exact hG.subgroup H

/-- There is an unconditional finitely presented non-operator-MF group. -/
theorem exists_finitelyPresented_nonOperatorMF :
    ∃ (G : Type) (_ : Group G),
      Group.IsFinitelyPresented G ∧ ¬IsOperatorMF G :=
  ChosenNonMFTheorem.exists_finitelyPresented_not_isOperatorMF

end MarkovMFConsequences
end GroupApproximation
