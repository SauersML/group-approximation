import GroupApproximation.Manuscript.NonMFSentences.FullDefectCornerRemark
import GroupApproximation.Meta.AxiomGuard

/-!
# Rings satisfying the printed hypothesis of the corner remark

`non_mf_groups_exist.tex`, the remark after `thm:full-defect-ring`, tex lines
1008-1014:

> The non-MF conclusion passes up from corners: if a nonzero idempotent
> $p\in R$ is such that the ring $pRp$, with unit $p$, satisfies the
> hypothesis, then $A\mapsto A+(1-p)I_n$ embeds $\EL_n(pRp)$ in $\EL_n(R)$,
> and restricting models shows that MF passes to subgroups, so $\EL_n(R)$ is
> not MF for every $n\ge2$.  The full-defect hypothesis itself need not pass
> to $R$, nor need every homomorphism from $\EL_n(R)$ to an MF group be
> trivial.

`FullDefectCornerRemark.FullDefectPair` is "the hypothesis", and
`manuscriptSentence_cornerPassesUp` takes it for the corner, as the sentence does.
This module exhibits rings that satisfy it: every universal Leavitt algebra
`L_k(1,d)` with `d ≥ 2`, in particular `L_{𝔽₂}(1,2)`, the ring used by
`manuscriptSentence_hypothesisNeedNotPass` for the second sentence.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace FullDefectCornerRemark

/-- **The printed hypothesis holds for `L_k(1,d)` with `d ≥ 2`.**  Take the pair
`s = s₀`, `t = t₀` of the canonical Leavitt family: `t₀s₀ = 1`, and `1 - s₀t₀` is
full because `t₁(1 - s₀t₀)s₁ = 1`. -/
theorem fullDefectPair_aryLeavittAlgebra (k : Type*) [Field k] (d : ℕ) (hd : 2 ≤ d) :
    FullDefectPair (AryLeavitt.AryLeavittAlgebra k d) := by
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    simp [i, j, Fin.ext_iff] at h
  obtain ⟨hts, m, a, b, hab⟩ :=
    GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRing.completeMatrixFamily_full
      (AryLeavitt.family k d) hij
  exact ⟨(AryLeavitt.family k d).left i, (AryLeavitt.family k d).right i, hts, m, a, b, hab⟩

/-- **The printed hypothesis holds for `L_{𝔽₂}(1,2)`.** -/
theorem fullDefectPair_aryLeavittAlgebra_zmodTwo :
    FullDefectPair (AryLeavitt.AryLeavittAlgebra (ZMod 2) 2) :=
  fullDefectPair_aryLeavittAlgebra (ZMod 2) 2 le_rfl

end FullDefectCornerRemark
end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMFSentences.FullDefectCornerRemark

#audit_axioms fullDefectPair_aryLeavittAlgebra
#audit_closed_axioms fullDefectPair_aryLeavittAlgebra_zmodTwo
