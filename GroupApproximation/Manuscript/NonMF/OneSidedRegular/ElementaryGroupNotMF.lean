import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingMaximal
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:one-sided-ring-maximal`: `EL_n(R)` is countable, nontrivial, and not MF

`non_mf_groups_exist.tex`, proof of `cor:one-sided-ring-maximal` (line 1072):

> If $R\ne0$ satisfies the hypothesis of Theorem~\ref{thm:full-defect-ring},
> then $G=\EL_n(R)$ is countable and nontrivial, and by
> Theorem~\ref{thm:full-defect-ring} it is not MF.

The rank is the one of the corollary's statement (line 1050): *for every
$n\ge2$*.  The hypothesis of `thm:full-defect-ring` (line 930) is: $R$ is a
countable unital ring with $ts=1$ and $R(1-st)R=R$, which is printed in the form
$1=\sum_j a_j(1-st)b_j$.

## Proof route

* *countable*: `FullDefectRing.countable_elementaryGroup`, since a matrix unit
  is determined by its finitely many entries in the countable ring `R`;
* *nontrivial*: `FullDefectRing.nontrivial_elementaryGroup` at the two distinct
  indices `0 ≠ 1` of `Fin n`, since `e₁₂(1) ≠ 1` over a nonzero ring;
* *not MF*: `thm:full-defect-ring` at every `n ≥ 2`, proved with nothing assumed
  as `FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics`,
  kills every homomorphism to an MF group; the identity of a nontrivial group is
  such a homomorphism if the group is MF
  (`FullDefectRing.not_isCDEOperatorMF_of_killsMFTargets`).  Both the
  countable-diagonal-embedding notion `IsCDEOperatorMF` and the
  operator-norm notion `IsOperatorMF` are recorded; they agree on countable
  groups (`isCDEOperatorMF_iff_isOperatorMF`).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace OneSidedRegular

open GroupApproximation.Manuscript.OneSidedMFRadical

/-- **`cor:one-sided-ring-maximal`, proof, line 1072.**  For a nonzero countable
unital ring `R` with `ts = 1` and `∑ₖ aₖ (1 - st) bₖ = 1`, and every `n ≥ 2`,
the group `G = EL_n(R)` is countable and nontrivial, and it is not MF (in both
the countable-embedding and the operator-norm sense). -/
theorem manuscriptSentence_elementaryGroupCountableNontrivialNotMF
    (R : Type) [Ring R] [Nontrivial R] [Countable R] (s t : R) (hts : t * s = 1)
    (hfull : ∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1)
    (n : ℕ) (hn : 2 ≤ n) :
    Countable (elementaryGroup (Fin n) R) ∧
      Nontrivial (elementaryGroup (Fin n) R) ∧
        ¬ @IsCDEOperatorMF (elementaryGroup (Fin n) R) _
            FullDefectRing.countable_elementaryGroup ∧
          ¬ IsOperatorMF (elementaryGroup (Fin n) R) := by
  haveI hcount : Countable (elementaryGroup (Fin n) R) :=
    FullDefectRing.countable_elementaryGroup
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have hne : (⟨0, h0⟩ : Fin n) ≠ ⟨1, h1⟩ := by
    intro hcon
    exact absurd (congrArg Fin.val hcon) (by norm_num)
  haveI : Nontrivial (elementaryGroup (Fin n) R) :=
    FullDefectRing.nontrivial_elementaryGroup (R := R) hne
  have hnotCDE : ¬ IsCDEOperatorMF (elementaryGroup (Fin n) R) :=
    FullDefectRing.not_isCDEOperatorMF_of_killsMFTargets fun M _ hM f x ↦
      FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics
        R s t hts hfull n hn M hM f x
  refine ⟨hcount, inferInstance, hnotCDE, ?_⟩
  intro hMF
  exact hnotCDE ((isCDEOperatorMF_iff_isOperatorMF (elementaryGroup (Fin n) R)).mpr hMF)

end OneSidedRegular
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.OneSidedRegular.manuscriptSentence_elementaryGroupCountableNontrivialNotMF
