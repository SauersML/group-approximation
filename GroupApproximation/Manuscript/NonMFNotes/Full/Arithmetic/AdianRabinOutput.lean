import GroupApproximation.Manuscript.NonMFNotes.Full.Arithmetic.Reduction
import GroupApproximation.Computability.OperatorMFMarkovData
import GroupApproximation.Sofic.LiteralNonMFEndpoint

/-!
# The Adian--Rabin output group: free in the trivial case, `E` inside otherwise

Manuscript `non_mf_group_notes.tex`, proof of `cor:undecidable`:

> "if `u = 1` in `G_e`, then `Δ(e,u)` presents an MF group: the trivial group in
> the classical form, and a free group in the variant used here, a free group
> being residually finite and so MF by Lemma `lem:permanence`(2); and
> if `u ≠ 1` in `G_e`, then `G_e` embeds in the group presented by `Δ(e,u)`."

> "Apply `Δ` to the free product of the input presentation with a fixed
> presentation of `E` and to the input word.  The resulting presentation code
> is computable from the pair and presents an MF group exactly when the input
> word is trivial.  In the trivial case the output group is free and so MF.  In
> the nontrivial case the free product, and so `E`, embeds in the output group."

Lean reading.
* The code-level construction is `RawTransform.rawTransform e d u`: free-product
  the input code `e` with a fixed code `d`, then apply the variant construction
  to the word.  Its computability is `RawTransformPrimrec.computable_rawTransform`.
* For an arbitrary fixed code `d`, this file proves the two printed clauses at
  the level of groups: in the trivial case an explicit `MulEquiv` onto the free
  group `FreeGroup (Fin n)` (`outputFreeEquiv`, `output_free`); in the
  nontrivial case injective homomorphisms from the free product code and from
  `d` into the output group (`coprod_embeds`, `forbidden_embeds`).
* `literalCode` is a presentation code of the literal eight-generator group `E`
  (`LiteralNonMFPresentation.MarkedGroup`, `def:E`), and `literalMarkovData`
  runs the general Adian--Rabin theorem `AdianRabinGeneral.reduction` with that
  code as the fixed factor.  `notesAdianRabinMap` is the printed map `Δ` with
  *all* its printed properties: computable, free output in the trivial case, `E`
  embedded in the output in the nontrivial case, and MF exactly when the word is
  trivial.
-/

namespace GroupApproximation.Full.NN11

open PresentationCodes MFRecognitionSecondLevel

/-! ## Composition of embeddings -/

/-- Injective homomorphisms compose. -/
theorem exists_injective_comp {A B C : Type*} [Group A] [Group B] [Group C]
    (g : B →* C) (f : A →* B) (hg : Function.Injective g) (hf : Function.Injective f) :
    ∃ h : A →* C, Function.Injective h :=
  ⟨g.comp f, by rw [MonoidHom.coe_comp]; exact hg.comp hf⟩

/-! ## The two printed clauses, for an arbitrary fixed factor -/

section FixedFactor

variable (d : PresentationCode) (p : PresentationCode × List (ℕ × Bool))

/-- **Trivial case, as an explicit isomorphism** (proof of `cor:undecidable`,
`non_mf_group_notes.tex`): "In the trivial case the output group is free." -/
noncomputable def outputFreeEquiv (hp : AdianRabinWordProblem.wordProblemPred p) :
    Carrier (RawTransform.rawTransform p.1 d p.2) ≃*
      FreeGroup (RabinVariantPresentation.FreeGen (genCount (CoprodCode.coprodCode p.1 d))) :=
  (RawTransform.rawCarrierEquiv p.1 d p.2).trans
    ((RabinVariantCode.variantCodeEquiv (CoprodCode.coprodCode p.1 d)
        (CoprodCode.normWord p.1 p.2)).trans
      (RabinVariantMF.collapseEquiv _ _
        ((AdianRabinGeneral.coprod_mk_eq_one_iff d p.1 p.2).2 hp)).symm)

/-- **Trivial case** (proof of `cor:undecidable`, `non_mf_group_notes.tex`):
"In the trivial case the output group is free", on finitely many generators. -/
theorem output_free (hp : AdianRabinWordProblem.wordProblemPred p) :
    ∃ n : ℕ, Nonempty (Carrier (RawTransform.rawTransform p.1 d p.2) ≃* FreeGroup (Fin n)) :=
  ⟨genCount (CoprodCode.coprodCode p.1 d) + 1 + 1,
    ⟨(outputFreeEquiv d p hp).trans (FreeGroup.freeGroupCongr
      ((Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv))⟩⟩

/-- **Nontrivial case, the free product** (proof of `cor:undecidable`,
`non_mf_group_notes.tex`): "In the nontrivial case the free product ... embeds in
the output group." -/
theorem coprod_embeds (hp : ¬ AdianRabinWordProblem.wordProblemPred p) :
    ∃ ι : Carrier (CoprodCode.coprodCode p.1 d) →* Carrier (RawTransform.rawTransform p.1 d p.2),
      Function.Injective ι := by
  have hne : PresentedGroup.mk {y | y ∈ PresentationCodeList.relatorListOf
        (CoprodCode.coprodCode p.1 d)}
      (wordOf (CoprodCode.coprodCode p.1 d) (CoprodCode.normWord p.1 p.2)) ≠ 1 :=
    fun h => hp ((AdianRabinGeneral.coprod_mk_eq_one_iff d p.1 p.2).1 h)
  obtain ⟨i1, h1⟩ := exists_injective_comp
    (RabinVariantPresentation.srcToPres _ _)
    (PresentationCodeList.carrierEquivList (CoprodCode.coprodCode p.1 d)).toMonoidHom
    (RabinVariantPresentation.srcToPres_injective_of_ne_one _ _ hne)
    (PresentationCodeList.carrierEquivList (CoprodCode.coprodCode p.1 d)).injective
  obtain ⟨i2, h2⟩ := exists_injective_comp
    (RabinVariantCode.variantCodeEquiv (CoprodCode.coprodCode p.1 d)
      (CoprodCode.normWord p.1 p.2)).symm.toMonoidHom i1
    (RabinVariantCode.variantCodeEquiv (CoprodCode.coprodCode p.1 d)
      (CoprodCode.normWord p.1 p.2)).symm.injective h1
  exact exists_injective_comp
    (RawTransform.rawCarrierEquiv p.1 d p.2).symm.toMonoidHom i2
    (RawTransform.rawCarrierEquiv p.1 d p.2).symm.injective h2

/-- **Nontrivial case, the fixed factor** (proof of `cor:undecidable`,
`non_mf_group_notes.tex`): "... the free product, and so `E`, embeds in the
output group", for the fixed factor `d`. -/
theorem forbidden_embeds (hp : ¬ AdianRabinWordProblem.wordProblemPred p) :
    ∃ ι : Carrier d →* Carrier (RawTransform.rawTransform p.1 d p.2), Function.Injective ι := by
  obtain ⟨j, hj⟩ := coprod_embeds d p hp
  obtain ⟨i1, h1⟩ := exists_injective_comp
    (RabinConstructionSource.inclRight {y | y ∈ PresentationCodeList.relatorListOf p.1}
      {y | y ∈ PresentationCodeList.relatorListOf d})
    (PresentationCodeList.carrierEquivList d).toMonoidHom
    (RabinConstructionSource.inclRight_injective _ _)
    (PresentationCodeList.carrierEquivList d).injective
  obtain ⟨i2, h2⟩ := exists_injective_comp
    (CoprodCode.coprodCodeEquiv p.1 d).symm.toMonoidHom i1
    (CoprodCode.coprodCodeEquiv p.1 d).symm.injective h1
  exact exists_injective_comp j i2 hj h2

end FixedFactor

/-! ## The repository's transform (fixed factor `negativeCode`) -/

/-- The trivial-case clause for the map of `Full/Arithmetic/Reduction.lean`:
when the word is trivial, the output group of
`AdianRabinVariantTransform.reduction` is free. -/
theorem reduction_output_free (p : PresentationCode × List (ℕ × Bool))
    (hp : AdianRabinWordProblem.wordProblemPred p) :
    ∃ n : ℕ, Nonempty
      (Carrier (AdianRabinVariantTransform.reduction.transform p) ≃* FreeGroup (Fin n)) :=
  output_free AdianRabinVariantTransform.forbidden p hp

/-! ## The printed map, with a fixed presentation of `E` -/

/-- A presentation code of the literal group `E` of `def:E`. -/
noncomputable abbrev literalCode : PresentationCode :=
  (exists_code_mulEquiv LiteralNonMFPresentation.MarkedGroup).choose

/-- The code `literalCode` presents `E`. -/
noncomputable def literalCodeEquiv : Carrier literalCode ≃* LiteralNonMFPresentation.MarkedGroup :=
  (exists_code_mulEquiv LiteralNonMFPresentation.MarkedGroup).choose_spec.some

/-- `E` is not MF, read at its code. -/
theorem not_isOperatorMF_literalCode : ¬ IsOperatorMF (Carrier literalCode) := fun h =>
  LiteralNonMFEndpoint.literal_not_isOperatorMF
    (IsOperatorMF.comap h literalCodeEquiv.symm.toMonoidHom literalCodeEquiv.symm.injective)

/-- **Operator-MF as a Markov property with forbidden factor `E`**: the data the
general Adian--Rabin theorem consumes, with the literal `E` as fixed factor. -/
noncomputable def literalMarkovData :
    AdianRabinGeneral.MarkovData (fun (H : Type) (_ : Group H) ↦ IsOperatorMF H) where
  hereditary f hf hK := hK.comap f hf
  free α _ := OperatorMFMarkovData.isOperatorMF_freeGroup α
  positiveCode := PresentationCodes.positiveCode
  positive := PresentationCodes.isOperatorMF_positiveCode
  forbidden := literalCode
  forbidden_not := not_isOperatorMF_literalCode

/-- **The printed map `Δ` of the proof of `cor:undecidable`, with every printed
property** (`non_mf_group_notes.tex`): applied to the free product of the input
presentation with a fixed presentation of `E` and to the input word, the output
code is computable from the pair; in the trivial case the output group is free;
in the nontrivial case `E` embeds in the output group; and the output presents
an MF group exactly when the input word is trivial. -/
theorem notesAdianRabinMap :
    ∃ delta : PresentationCode × List (ℕ × Bool) → PresentationCode,
      Computable delta ∧
      ∀ p : PresentationCode × List (ℕ × Bool),
        (AdianRabinWordProblem.wordProblemPred p →
          ∃ n : ℕ, Nonempty (Carrier (delta p) ≃* FreeGroup (Fin n))) ∧
        (¬ AdianRabinWordProblem.wordProblemPred p →
          ∃ ι : LiteralNonMFPresentation.MarkedGroup →* Carrier (delta p),
            Function.Injective ι) ∧
        (MFCode (delta p) ↔ AdianRabinWordProblem.wordProblemPred p) := by
  refine ⟨fun p => RawTransform.rawTransform p.1 literalCode p.2,
    (AdianRabinGeneral.reduction literalMarkovData).transform_computable, fun p => ⟨?_, ?_, ?_⟩⟩
  · exact output_free literalCode p
  · intro hp
    obtain ⟨j, hj⟩ := forbidden_embeds literalCode p hp
    exact exists_injective_comp j literalCodeEquiv.symm.toMonoidHom hj
      literalCodeEquiv.symm.injective
  · exact AdianRabinGeneral.correct_raw literalMarkovData p

/-- **The reduction through `E`** (`thm:mf-arithmetic`, "Moreover" clause, with
the printed fixed factor): the complement of the uniform word problem many-one
reduces to `NONMF_fp` by the map `Δ` built from `E`. -/
theorem wordProblemCompl_manyOneReduces_nonMF_viaE :
    (fun x => ¬ AdianRabinWordProblem.wordProblemPred x) ≤₀ NonMFCode := by
  obtain ⟨delta, hdelta, hspec⟩ := notesAdianRabinMap
  exact ⟨delta, hdelta, fun p => not_congr (hspec p).2.2.symm⟩

#audit_axioms GroupApproximation.Full.NN11.output_free
#audit_axioms GroupApproximation.Full.NN11.coprod_embeds
#audit_axioms GroupApproximation.Full.NN11.forbidden_embeds
#audit_axioms GroupApproximation.Full.NN11.reduction_output_free
#audit_closed_axioms GroupApproximation.Full.NN11.notesAdianRabinMap
#audit_closed_axioms GroupApproximation.Full.NN11.wordProblemCompl_manyOneReduces_nonMF_viaE
#audit_axioms GroupApproximation.Full.NN11.not_isOperatorMF_literalCode

end GroupApproximation.Full.NN11
