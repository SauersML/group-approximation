import GroupApproximation.Computability.WordProblemRE
import GroupApproximation.Computability.MFRecognitionSecondLevel
import GroupApproximation.Meta.AxiomGuard

/-!
# The many-one reduction from the uniform word problem to MF recognition

Manuscript `non_mf_group_notes.tex`, proof of `cor:undecidable` and the last
sentence of `thm:mf-arithmetic`:

> "Apply `Δ` to the free product of the input presentation with a fixed
> presentation of `E` and to the input word.  The resulting presentation code
> is computable from the pair and presents an MF group exactly when the input
> word is trivial."

> "Moreover the complement of the uniform word problem many-one reduces to
> `NONMF_fp`."

The computable map is the repository's Adian--Rabin variant transformation
`AdianRabinVariantTransform.reduction` (list surgery on codes, with
computability `RawTransformPrimrec.computable_rawTransform` and correctness
`AdianRabinVariantTransform.correct_raw`).  Its forbidden factor is the
repository's fixed finitely presented non-MF code
`PresentationCodes.negativeCode`; in the trivial case the output group is
residually finite and so MF, in the nontrivial case the forbidden factor
embeds and the output is not MF.  This file only packages that datum as
Mathlib's `ManyOneReducible` (`≤₀`) on the concrete code type
`PresentationCodes.PresentationCode`, which is the type used by
`MFRecognitionSecondLevel.{MFCode, NonMFCode}`, and derives the consequences
used by the manuscript: undecidability and non-enumerability transport along
the reduction.

The word predicate is `AdianRabinWordProblem.wordProblemPred`, on pairs
(presentation code, raw word).  A raw word is a list of letters `(i, ε)`, and
the letter index is read modulo the generator count of the code
(`PresentationCodes.letterOf`), so every raw word is a word in the generators
of that code.
-/

namespace GroupApproximation.Full.NN11

open PresentationCodes MFRecognitionSecondLevel

/-! ## Generic transport lemmas -/

/-- An Adian--Rabin reduction datum is a computable many-one reduction. -/
theorem manyOneReducible_of_adianRabinReduction
    {Source Code : Type*} [Primcodable Source] [Primcodable Code]
    {p : Source → Prop} {q : Code → Prop}
    (R : MarkovMFConsequences.AdianRabinReduction p q) : p ≤₀ q :=
  ⟨R.transform, R.transform_computable, fun s => (R.correct s).symm⟩

/-- "the preimage of a recursively enumerable set under a computable map is
recursively enumerable", contraposed: a predicate that many-one reduces a
non-RE predicate is not RE. -/
theorem not_rePred_of_manyOneReducible
    {α β : Type*} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop}
    (h : p ≤₀ q) (hp : ¬ REPred p) : ¬ REPred q := by
  intro hq
  obtain ⟨f, hf, hcorrect⟩ := h
  exact hp ((MarkovMFConsequences.rePred_comp hq hf).of_eq fun a => (hcorrect a).symm)

/-! ## The reduction at the concrete coding -/

/-- **The effective Adian--Rabin map** (proof of `cor:undecidable`,
`non_mf_group_notes.tex`): the uniform word problem many-one reduces to MF
recognition on finite presentation codes.  The output code presents an MF group
exactly when the input word is trivial in the input group. -/
theorem wordProblem_manyOneReduces_mf :
    AdianRabinWordProblem.wordProblemPred ≤₀ MFCode :=
  ⟨AdianRabinVariantTransform.reduction.transform,
    AdianRabinVariantTransform.reduction.transform_computable,
    fun x => (AdianRabinVariantTransform.reduction.correct x).symm.trans
      (operatorMFProperty_semantics _)⟩

/-- **`thm:mf-arithmetic`, "Moreover" clause** (`non_mf_group_notes.tex`): the
complement of the uniform word problem many-one reduces to `NONMF_fp`, by the
same computable map. -/
theorem wordProblemCompl_manyOneReduces_nonMF :
    (fun x => ¬ AdianRabinWordProblem.wordProblemPred x) ≤₀ NonMFCode :=
  ArithmeticalHierarchy.manyOneReducible_compl wordProblem_manyOneReduces_mf

/-- The computable map of the reduction, in the manuscript's displayed form:
a computable `Δ` from (code, word) pairs to codes with `G_{Δ(e,u)}` MF exactly
when `u = 1` in `G_e`. -/
theorem exists_computable_adianRabin_map :
    ∃ delta : PresentationCode × List (ℕ × Bool) → PresentationCode,
      Computable delta ∧
        ∀ x, MFCode (delta x) ↔ AdianRabinWordProblem.wordProblemPred x := by
  obtain ⟨f, hf, hcorrect⟩ := wordProblem_manyOneReduces_mf
  exact ⟨f, hf, fun x => (hcorrect x).symm⟩

/-! ## Consequences along the reduction -/

/-- **`cor:undecidable`(2), by the printed route**: "Composing a decision
procedure for MF recognition with this map would then decide `W`, so no such
procedure exists." -/
theorem mfCode_not_computable_via_reduction : ¬ ComputablePred MFCode := fun h =>
  Computability.not_computablePred_wordProblemPred
    (ComputablePred.computable_of_manyOneReducible wordProblem_manyOneReduces_mf h)

/-- **`cor:undecidable`(3), non-MF clause, by the printed route**: "the
preimage of the set of non-MF presentation codes under this computable map is
exactly the set of pairs outside `W`, and the preimage of a recursively
enumerable set under a computable map is recursively enumerable." -/
theorem nonMFCode_not_re_via_reduction : ¬ REPred NonMFCode :=
  not_rePred_of_manyOneReducible wordProblemCompl_manyOneReduces_nonMF
    WordProblemRE.not_rePred_compl_wordProblemPred

#audit_closed_axioms GroupApproximation.Full.NN11.wordProblem_manyOneReduces_mf
#audit_closed_axioms GroupApproximation.Full.NN11.wordProblemCompl_manyOneReduces_nonMF
#audit_closed_axioms GroupApproximation.Full.NN11.exists_computable_adianRabin_map
#audit_axioms GroupApproximation.Full.NN11.mfCode_not_computable_via_reduction
#audit_axioms GroupApproximation.Full.NN11.nonMFCode_not_re_via_reduction

end GroupApproximation.Full.NN11
