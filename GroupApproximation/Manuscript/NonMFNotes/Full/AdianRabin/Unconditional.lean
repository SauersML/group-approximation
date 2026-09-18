import GroupApproximation.Computability.AdianRabinVariantTransform
import GroupApproximation.Computability.BooneWordProblemUndecidable
import GroupApproximation.Computability.WordProblemRE

/-!
# Unconditional Adian--Rabin endpoints for `cor:undecidable`

Manuscript: `non_mf_group_notes.tex`, Corollary `cor:undecidable`
(undecidability of MF recognition), clauses (2) and (3).

`Computability.AdianRabinVariantTransform` states the Adian--Rabin transfer in
hypothesis-taking form:

* `operatorMF_recognition_undecidable_of_wordProblem` needs
  `¬ ComputablePred wordProblemPred`;
* `operatorMF_negative_side_not_re_of_wordProblem` needs
  `¬ REPred (fun x => ¬ wordProblemPred x)`.

This file instantiates both transfers, so that the endpoints carry no hypothesis
binder.  The first hypothesis is Boone's undecidable word problem in exactly the
form `Computability.not_computablePred_wordProblemPred` proves.  The second is
adapted from it by Post's theorem against the recursive enumerability of the
word problem (`WordProblemRE.rePred_wordProblemPred`), which is recorded below as
`not_rePred_compl_wordProblemPred`.
-/

namespace GroupApproximation.Full.NN13AR

/-- **Boone: the uniform word problem on presentation codes is undecidable.**
The input of the first Adian--Rabin transfer, in the form that transfer takes.
(`non_mf_group_notes.tex`, `cor:undecidable`(1).) -/
theorem wordProblem_not_computable :
    ¬ ComputablePred GroupApproximation.AdianRabinWordProblem.wordProblemPred :=
  GroupApproximation.Computability.not_computablePred_wordProblemPred

/-- **Adapter: the complement of the word problem is not recursively enumerable.**
Post's theorem: the word problem is r.e. (`WordProblemRE.rePred_wordProblemPred`),
so an r.e. complement would make it decidable, contradicting Boone's theorem
`wordProblem_not_computable`.  This is the hypothesis of the second Adian--Rabin
transfer, in the form that transfer takes.
(`non_mf_group_notes.tex`, `cor:undecidable`(3).) -/
theorem not_rePred_compl_wordProblemPred :
    ¬ REPred fun x => ¬ GroupApproximation.AdianRabinWordProblem.wordProblemPred x :=
  GroupApproximation.WordProblemRE.not_rePred_compl_wordProblemPred_of_not_computablePred
    wordProblem_not_computable

/-- **MF recognition is undecidable, unconditionally.**
`AdianRabinVariantTransform.operatorMF_recognition_undecidable_of_wordProblem`
instantiated at Boone's undecidable word problem.
(`non_mf_group_notes.tex`, `cor:undecidable`(2).) -/
theorem operatorMF_recognition_undecidable :
    ¬ ComputablePred
      (GroupApproximation.MarkovMFConsequences.operatorMFProperty
        GroupApproximation.PresentationCodes.semantics) :=
  GroupApproximation.AdianRabinVariantTransform.operatorMF_recognition_undecidable_of_wordProblem
    wordProblem_not_computable

/-- **The presentation codes of non-MF groups are not recursively enumerable,
unconditionally.**
`AdianRabinVariantTransform.operatorMF_negative_side_not_re_of_wordProblem`
instantiated at the adapter `not_rePred_compl_wordProblemPred`.
(`non_mf_group_notes.tex`, `cor:undecidable`(3).) -/
theorem operatorMF_negative_side_not_re :
    ¬ REPred fun code =>
      ¬ GroupApproximation.MarkovMFConsequences.operatorMFProperty
        GroupApproximation.PresentationCodes.semantics code :=
  GroupApproximation.AdianRabinVariantTransform.operatorMF_negative_side_not_re_of_wordProblem
    not_rePred_compl_wordProblemPred

end GroupApproximation.Full.NN13AR
