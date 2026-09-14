import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingMaximal
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:one-sided-ring-maximal`: `EL_n(R)` is countable, nontrivial and not MF, at every `n ≥ 2`

`non_mf_groups_exist.tex`, proof of Corollary `cor:one-sided-ring-maximal` (tex 1060–1062, census row
`2ff745dd7064`):

> If $R\ne0$ satisfies the hypothesis of Theorem~\ref{thm:full-defect-ring}, then $G=\EL_n(R)$ is countable
> and nontrivial, and by Theorem~\ref{thm:full-defect-ring} it is not MF.

`FullDefectRing.PrintedElementaryGroupNotMF` states the conclusion at `n ≥ 4` and displays no nontriviality
clause.  This module states the sentence at the corollary's `n ≥ 2`, with both displayed clauses, and proves it
with nothing assumed.

* Countability: `countable_elementaryGroup`.
* Nontriviality: `nontrivial_elementaryGroup`, since `e₁₂(1) ≠ 1` over a nonzero ring.
* Not MF: Theorem `thm:full-defect-ring` at rank two
  (`FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics`) kills every
  homomorphism to an MF group, and `not_isCDEOperatorMF_of_killsMFTargets` turns that into "not MF" for a
  nontrivial countable group.
-/

namespace GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRing

/-- **"then $G=\EL_n(R)$ is countable and nontrivial, and by Theorem~\ref{thm:full-defect-ring} it is not MF"**
(tex 1060–1062), for every countable nonzero ring with `ts = 1` and full `1 - st`, at every `n ≥ 2`. -/
def PrintedElementaryGroupNotMFRankTwo : Prop :=
  ∀ (R : Type) [Ring R] [Nontrivial R] [Countable R] (s t : R), t * s = 1 →
    (∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) →
      ∀ (n : ℕ), 2 ≤ n →
        Countable (elementaryGroup (Fin n) R) ∧ Nontrivial (elementaryGroup (Fin n) R) ∧
          ¬ @IsCDEOperatorMF (elementaryGroup (Fin n) R) _ countable_elementaryGroup

theorem printedElementaryGroupNotMFRankTwo : PrintedElementaryGroupNotMFRankTwo := by
  intro R _ _ _ s t hts hfull n hn
  haveI : Countable (elementaryGroup (Fin n) R) := countable_elementaryGroup
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have hne : (⟨0, h0⟩ : Fin n) ≠ ⟨1, h1⟩ := by
    intro hcon
    exact absurd (congrArg Fin.val hcon) (by norm_num)
  haveI : Nontrivial (elementaryGroup (Fin n) R) := nontrivial_elementaryGroup (R := R) hne
  refine ⟨inferInstance, inferInstance, ?_⟩
  exact not_isCDEOperatorMF_of_killsMFTargets fun M _ hM f x ↦
    FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics
      R s t hts hfull n hn M hM f x

end GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRing

#audit_closed_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRing.printedElementaryGroupNotMFRankTwo
