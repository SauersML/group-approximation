import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:mf-quotient-units`: the two inclusions between `N` and `ker κ`

`non_mf_groups_exist.tex`, proof of Theorem `thm:mf-quotient-units`, with
`H = R^×`, `N = Rad_MF(H)` and `κ : R^× → K_1(R)`.

## Sentence at tex 1251 (census key `23b488384d1b`)

> So `κ` is a homomorphism to an MF group, and `N ≤ ker κ`.

The census decl `MFQuotientUnitsSentences.manuscriptSentence_radicalLeKerKappa`
states `N ≤ ker κ` for an arbitrary homomorphism into a countable abelian group.
It does not state the first clause, that the target `K_1(R)` of the *actual*
`κ` is MF.
`manuscriptSentence_kappaTargetMFAndRadicalLeKer` states both clauses for the
actual `κ = AlgebraicK.kappa R`.

Route: `K_1(R)` is a countable abelian group (`AlgebraicK.algebraicKOneCommGroup`,
`AlgebraicK.algebraicKOne_countable`), hence MF
(`manuscriptSentence_countableAbelianIsMF`), and the radical lies in the kernel of
every homomorphism to an MF group (`manuscriptSentence_radicalLeKerKappa`).

## Sentence at tex 1308 (census key `95141daa8321`)

> Hence `ker κ ≤ N`.

The census decls give `N = [H,H]` and the whole theorem, not the printed
inclusion. `manuscriptSentence_kerKappaLeRadical` states the inclusion
literally. It holds for every countable purely infinite simple ring `R`, which
is the theorem's standing hypothesis.

Route: `ker κ = [H,H]` (AGP, proved as
`manuscriptSentence_kappaSurjectiveKernelCommutator`) and `N = [H,H]`
(`manuscriptSentence_conclusion`, which is proved through the corner-unit
reduction the printed converse carries out).
-/

namespace GroupApproximation.Manuscript.NonMF.AuditBinaryUnits

/-- **Printed (tex 1251):** "So `κ` is a homomorphism to an MF group, and
`N ≤ ker κ`."  For every countable unital ring `R`, the target `K_1(R)` of
`κ : R^× → K_1(R)` is MF, and `Rad_MF(R^×) ≤ ker κ`. -/
theorem manuscriptSentence_kappaTargetMFAndRadicalLeKer (R : Type) [Ring R] [Countable R] :
    GroupApproximation.IsOperatorMF (GroupApproximation.AlgebraicK.AlgebraicKOne R) ∧
      GroupApproximation.MFQuotientUnits.mfHomKernel Rˣ
        ≤ (GroupApproximation.AlgebraicK.kappa R).ker :=
  ⟨GroupApproximation.MFQuotientUnitsSentences.manuscriptSentence_countableAbelianIsMF
      (GroupApproximation.AlgebraicK.AlgebraicKOne R),
    GroupApproximation.MFQuotientUnitsSentences.manuscriptSentence_radicalLeKerKappa
      (GroupApproximation.AlgebraicK.kappa R)⟩

#audit_axioms manuscriptSentence_kappaTargetMFAndRadicalLeKer

/-- **Printed (tex 1308):** "Hence `ker κ ≤ N`."  For every countable purely
infinite simple ring `R`, `ker (κ : R^× → K_1(R)) ≤ Rad_MF(R^×)`. -/
theorem manuscriptSentence_kerKappaLeRadical (R : Type) [Ring R] [Countable R]
    (hR : GroupApproximation.MFQuotientUnits.IsPurelyInfiniteSimpleRing R) :
    (GroupApproximation.AlgebraicK.kappa R).ker
      ≤ GroupApproximation.MFQuotientUnits.mfHomKernel Rˣ := by
  intro x hx
  rw [(GroupApproximation.MFQuotientUnitsSentences.manuscriptSentence_kappaSurjectiveKernelCommutator
    R hR).2] at hx
  rw [GroupApproximation.MFQuotientUnitsSentences.manuscriptSentence_conclusion R hR]
  exact hx

#audit_axioms manuscriptSentence_kerKappaLeRadical

end GroupApproximation.Manuscript.NonMF.AuditBinaryUnits
