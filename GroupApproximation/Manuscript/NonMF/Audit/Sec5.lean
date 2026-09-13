import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Manuscript.NonMF.AcylindricallyHyperbolic
import GroupApproximation.GGT.OsinLemma71Printed
import GroupApproximation.Manuscript.NonMF.SimpleInDefect
import GroupApproximation.Manuscript.NonMF.PrintedDefectParagraph
import GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences
import GroupApproximation.Manuscript.NonMF.TorsionFreeDefectNormalClosure
import GroupApproximation.Manuscript.NonMF.OsinTheorem12NonDegenerate
import GroupApproximation.Manuscript.NonMF.DGOTheorem235Proof
import GroupApproximation.Manuscript.NonMF.GerasimovaOsinTheorem11Closed
import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Analysis.ReducedGroupCStarTraceFaithful
import GroupApproximation.Analysis.ReducedGroupCStarStablyFinite
import GroupApproximation.Analysis.ReducedGroupCStarMFAlgebra

/-!
# Audit gate: `sec:torsion-free`, Origin and authorship, Acknowledgments

`non_mf_groups_exist.tex` lines 1621–2022.

Every census row in this range with status `formalized` or `definition` names Lean
declarations.  Each one is audited below, so a widened axiom closure, or a declaration
that has been lost or renamed, becomes a build error in this module.

* `#audit_closed_axioms` is used on named-proposition endpoints, whose type is a
  `def … : Prop` rather than a leading binder.
* `#audit_axioms` is used on every other carrier: definitions, and sentence-level lemmas
  whose hypotheses are the printed setup or the conclusions of earlier sentences.

Each group of lines names its census row id and tex line.  After a row's own
declarations come the route theorems that carry the cited step it rests on.

Rows with status `partial` belong to lanes still working on the walls and are not
gated here.  The provenance and attribution rows (tex 1738–1789) name no declaration.
-/

/-! ## L1629 `615720614d7a` (definition): suitable subgroups -/

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFree.Suitable

/-! ## L1659 `c650b0a20b89`: `N` is infinite, non-elementary by Osin 7.1, suitable -/

#audit_closed_axioms GroupApproximation.GGT.OsinPrinted.manuscriptSentence_saturationOsinClosed
#audit_closed_axioms GroupApproximation.GGT.OsinPrinted.osinLemma71Printed
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences.manuscriptSentence_saturationSuitable

/-! ## L1659 `24d44fae17ad`: the display `Q = ⟨φ(gᵢ)⟩ ≤ φ(N₀) ≤ φ(N) ≤ Q` -/

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences.manuscriptSentence_saturationDisplay

/-! ## L1659 `c3246ffe1961`: the quotient is torsion-free and finitely presented -/

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences.manuscriptSentence_saturationQuotientTorsionFree
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences.manuscriptSentence_saturationQuotientFinitelyPresented

/-! ## L1675 `02b6bf87400f`, `26237422bf4c`: `S = tJt⁻¹`; `J` and `S` are perfect -/

#audit_axioms GroupApproximation.Manuscript.NonMF.PrintedFournierFacioData.conjFactor
#audit_axioms GroupApproximation.Manuscript.NonMF.PrintedFournierFacioData.commutator_simpleFactor_eq
#audit_axioms GroupApproximation.Manuscript.NonMF.PrintedFournierFacioData.commutator_conjFactor_eq

/-! ## L1687 `8e8d5f3f8be0`, `d8d9d495865d`: `S ≤ 𝔇_{G₀}(Γ)` -/

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.defect_generator_mem_of_simpleFactor
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.commutator_conjFactor_le_printedDefect
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.conjFactor_le_printedDefect
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.manuscriptSimpleFactorInDefect

/-! ## L1697 `56f937d2ec19`: `N` is nontrivial -/

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences.manuscriptSentence_theoremNormalClosureNeBot

/-! ## L1697 `9d87872de931`: `Q` is infinite and has property (T) -/

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences.manuscriptSentence_theoremQuotientInfinite
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences.manuscriptSentence_theoremQuotientKazhdan

/-! ## L1705 `da4a1c0beff4`: `φ(S) ≤ 𝔇_Q(φ(Γ))` by `eq:defect-functorial` -/

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences.manuscriptSentence_theoremDefectFunctorial
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.map_conjFactor_le_printedDefect_of_functorial
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.manuscriptLemmaCommutatorInDefect

/-! ## L1705 `d29816e1de56`: `𝔇_Q(φ(Γ))` is normal, the normal closure of `φ(S)` is
`φ(N) = Q`, so `𝔇_Q(φ(Γ)) = Q` -/

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences.manuscriptSentence_theoremDefectEqTop
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeDefectNormalClosure.manuscriptSentence_theoremNormalClosureDefectEqTop
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeDefectNormalClosure.printedNormalClosureDefectEqTop

/-! ## L1711 `eef4d274766e`, `871771af6cba`: both have (T); homomorphisms to MF groups
are trivial; an MF quotient is trivial -/

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences.manuscriptSentence_theoremBothKazhdan
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences.manuscriptSentence_theoremHomsTrivial
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences.manuscriptSentence_theoremQuotientTrivial

/-! ## L1725 `92115dd7edef`: a non-degenerate hyperbolically embedded subgroup, no
nontrivial finite normal subgroup -/

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.exists_isNonDegenerate_isHypEmbedded
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.osinTheorem12Printed_unconditional
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences.manuscriptSentence_algebraTrivialFiniteRadical

/-! ## L1725 `b7b49212cd37`: separable, generated by two unitaries, stably finite by the
faithful canonical trace, not MF by `prop:mf-residual-calculus` -/

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences.manuscriptSentence_algebraSeparableGenerated
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences.manuscriptSentence_algebraStablyFinite
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences.manuscriptSentence_algebraNotMF
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrintedSentences.manuscriptSentence_algebraNotCDEOperatorMF
#audit_axioms GroupApproximation.ReducedGroupCStarTrace.canonicalFaithfulTracialState
#audit_axioms GroupApproximation.reducedGroupCStar_isStablyFiniteCStarAlgebra
#audit_axioms GroupApproximation.isCDEOperatorMF_of_faithful_corona_map
#audit_axioms GroupApproximation.HasMFEmbedding.isCDEOperatorMF
#audit_axioms GroupApproximation.not_isMFAlgebra_reducedGroupCStar

/-! ## L1725 `f2bf6328169e` (partial, another lane): the two cited theorems, proved -/

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.dgoTheorem235Printed
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TorsionFreePrinted.gerasimovaOsinTheorem11Printed
