import GroupApproximation.Manuscript.NonMFNotes.Full.Arithmetic.Reduction
import GroupApproximation.Computability.OperatorMFMarkovWitness
import GroupApproximation.Sofic.LiteralNonMFEndpoint

/-!
# `cor:undecidable`: undecidability of MF recognition

Manuscript `non_mf_group_notes.tex`, subsection "Undecidability of MF
recognition".

The Markov paragraph before the corollary:

> "MF is a Markov property of finitely presented groups: the trivial group is
> MF, while by subgroup heredity the finitely presented group `E` embeds in no
> MF group."

`cor:undecidable`:

> "Write `W` for the predicate on pairs consisting of a presentation code and a
> word in the generators of that code, holding when the word is trivial in the
> presented group.  Then:
> (1) `W` is undecidable;
> (2) no algorithm decides, from a presentation code, whether the presented
> group is MF;
> (3) `W` is recursively enumerable, whereas its complement and the set of
> presentation codes of non-MF groups are not."

Lean reading.
* The effective coding is `PresentationCodes.PresentationCode`, with presented
  group `PresentationCodes.Carrier c`; `W` is
  `AdianRabinWordProblem.wordProblemPred` on (code, raw word) pairs.
* "algorithm decides" is Mathlib's `ComputablePred`; "recursively enumerable"
  is Mathlib's `REPred`.
* `E` is the literal eight-generator group `LiteralNonMFPresentation.MarkedGroup`
  of `def:E`.

Proof sources.
* (1) is `Computability.not_computablePred_wordProblemPred`, whose undecidable
  source is Mathlib's halting problem, through the in-repository Boone
  construction (no hypothesis).
* (2) and the non-MF half of (3) are derived along the printed route from the
  many-one reduction of `Full/Arithmetic/Reduction.lean`.
* `W ∈ RE` is `WordProblemRE.rePred_wordProblemPred` (finite certificates),
  and the complement clause is `WordProblemRE.not_rePred_compl_wordProblemPred`
  (Post's theorem against (1)).
-/

namespace GroupApproximation.Full.NN11

open PresentationCodes MFRecognitionSecondLevel

/-- **Markov paragraph before `cor:undecidable`** (`non_mf_group_notes.tex`):
the trivial group is MF, and the literal group `E` embeds in no MF group. -/
theorem notesMarkovProperty :
    IsOperatorMF PUnit.{1} ∧
      ∀ (G : Type) [Group G] (ι : LiteralNonMFPresentation.MarkedGroup →* G),
        Function.Injective ι → ¬ IsOperatorMF G := by
  refine ⟨OperatorMFMarkovWitness.positive_punit.2, ?_⟩
  intro _ _ ι hι hG
  exact LiteralNonMFEndpoint.literal_not_isOperatorMF (IsOperatorMF.comap hG ι hι)

/-- The literal group `E` has a presentation code, and that code is a non-MF
code ("the finitely presented group `E`", `non_mf_group_notes.tex`). -/
theorem notesLiteralCode :
    ∃ c : PresentationCode,
      Nonempty (Carrier c ≃* LiteralNonMFPresentation.MarkedGroup) ∧ NonMFCode c := by
  obtain ⟨c, ⟨e⟩⟩ := PresentationCodes.exists_code_mulEquiv LiteralNonMFPresentation.MarkedGroup
  refine ⟨c, ⟨e⟩, ?_⟩
  intro h
  exact LiteralNonMFEndpoint.literal_not_isOperatorMF
    (IsOperatorMF.comap h e.symm.toMonoidHom e.symm.injective)

/-- **`cor:undecidable`(1)--(3), as one closed conjunction**
(`non_mf_group_notes.tex`):

1. `W` is undecidable;
2. MF recognition on presentation codes is undecidable;
3. `W` is recursively enumerable, its complement is not, and the set of codes of
   non-MF groups is not.

No hypothesis and no literature input. -/
theorem notesUndecidable :
    ¬ ComputablePred AdianRabinWordProblem.wordProblemPred ∧
      ¬ ComputablePred MFCode ∧
      (REPred AdianRabinWordProblem.wordProblemPred ∧
        ¬ REPred (fun x => ¬ AdianRabinWordProblem.wordProblemPred x) ∧
        ¬ REPred NonMFCode) :=
  ⟨Computability.not_computablePred_wordProblemPred,
    mfCode_not_computable_via_reduction,
    WordProblemRE.rePred_wordProblemPred,
    WordProblemRE.not_rePred_compl_wordProblemPred,
    nonMFCode_not_re_via_reduction⟩

/-- **`cor:undecidable` together with the data of its proof**
(`non_mf_group_notes.tex`): the Markov witnesses, the three clauses, and the
computable Adian--Rabin map `Δ` with `G_{Δ(e,u)}` MF exactly when `u = 1` in
`G_e`. -/
theorem notesUndecidableWithProof :
    (IsOperatorMF PUnit.{1} ∧
      ∀ (G : Type) [Group G] (ι : LiteralNonMFPresentation.MarkedGroup →* G),
        Function.Injective ι → ¬ IsOperatorMF G) ∧
    (¬ ComputablePred AdianRabinWordProblem.wordProblemPred ∧
      ¬ ComputablePred MFCode ∧
      (REPred AdianRabinWordProblem.wordProblemPred ∧
        ¬ REPred (fun x => ¬ AdianRabinWordProblem.wordProblemPred x) ∧
        ¬ REPred NonMFCode)) ∧
    (∃ delta : PresentationCode × List (ℕ × Bool) → PresentationCode,
      Computable delta ∧
        ∀ x, MFCode (delta x) ↔ AdianRabinWordProblem.wordProblemPred x) :=
  ⟨notesMarkovProperty, notesUndecidable, exists_computable_adianRabin_map⟩

#audit_closed_axioms GroupApproximation.Full.NN11.notesMarkovProperty
#audit_closed_axioms GroupApproximation.Full.NN11.notesLiteralCode
#audit_closed_axioms GroupApproximation.Full.NN11.notesUndecidable
#audit_closed_axioms GroupApproximation.Full.NN11.notesUndecidableWithProof

end GroupApproximation.Full.NN11
