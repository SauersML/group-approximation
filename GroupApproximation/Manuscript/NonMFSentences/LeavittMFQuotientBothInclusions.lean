import GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDecompositionClosed
import GroupApproximation.Manuscript.OneSidedMFRadical.LeavittMFQuotientGeneral
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:leavitt-mf-quotient`: `[H,H] ≤ EL_d(R)` and `EL_d(R) ≤ [H,H]`

`non_mf_groups_exist.tex`, line 1307, the last sentence of the proof of the corollary
`\label{cor:leavitt-mf-quotient}` (Leavitt unit groups, tex 1297), census row `f6962254d259`:

> So `[H,H] ≤ EL_d(R)`, while `EL_d(R) ≤ [H,H]` because every homomorphism from `EL_d(R)`
> to an MF group is trivial (Theorem `thm:full-defect-ring`).

Here `k` is a countable field, `d ≥ 2`, `R = L_k(1,d)` is `AryLeavitt.AryLeavittAlgebra k d`,
and `H` is read as `GL_d(R)` through the identification `H ≅ GL_d(R)` of the first sentence
of the proof (`LeavittMFQuotientUnitsGL`).

The module carries the three clauses of the sentence along the printed route.

* "So `[H,H] ≤ EL_d(R)`" is the consequence of the Khanh--Thanh decomposition
  `GL_d(R) = EL_d(R)D_d(k)`, with `D_d(k)` abelian and normalizing `EL_d(R)`, closed as
  `KhanhThanhDiagonal.manuscriptSentence_commutatorInElementaryPrinted`.
* "every homomorphism from `EL_d(R)` to an MF group is trivial" is `thm:full-defect-ring` at
  `R = L_k(1,d)` and rank `n = d`, closed as
  `FullDefectRingEJZUnconditional.manuscriptLeavittAlgebraFullDefectRankTwoAllCharacteristics`.
  It is stated for homomorphisms out of the subgroup `EL_d(R)` itself, as printed, and not
  only for restrictions of homomorphisms out of `GL_d(R)`.
* "while `EL_d(R) ≤ [H,H]` because ..." is `elementary_le_commutator_of_trivial`: a
  homomorphism from `GL_d(R)` to an MF group restricts to `EL_d(R)`, so it kills `EL_d(R)`;
  and an element of the countable group `GL_d(R)` killed by every homomorphism to an MF group
  lies in `[GL_d(R),GL_d(R)]`, because the abelianization is countable and abelian, hence MF.

## Endpoint

* `PrintedLeavittBothInclusions`, `manuscriptSentence_bothInclusionsPrinted`: the three
  clauses at every countable field `k` and every `d ≥ 2`, with nothing assumed.
-/

namespace GroupApproximation
namespace LeavittMFQuotientBothInclusions

open AryLeavitt Manuscript.OneSidedMFRadical

/-- **"`EL_d(R) ≤ [H,H]` because every homomorphism from `EL_d(R)` to an MF group is
trivial"**, the printed implication.  A homomorphism `f` from `GL_d(R)` to an MF group
restricts to a homomorphism from `EL_d(R)`, which is trivial; so every element of `EL_d(R)`
is killed by every such `f`, and in the countable group `GL_d(R)` such an element lies in
the commutator subgroup (`LeavittMFQuotientGeneral.mfKernels_le_commutator`). -/
theorem elementary_le_commutator_of_trivial (k : Type) [Field k] [Countable k] (d : ℕ)
    (hEL : ∀ (M : Type) [Group M], IsOperatorMF M →
      ∀ (f : elementaryGroup (Fin d) (AryLeavittAlgebra k d) →* M)
        (x : elementaryGroup (Fin d) (AryLeavittAlgebra k d)), f x = 1) :
    elementaryGroup (Fin d) (AryLeavittAlgebra k d) ≤
      commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ := by
  intro x hx
  exact LeavittMFQuotientGeneral.mfKernels_le_commutator fun M _ hM f ↦
    hEL M hM (f.comp (elementaryGroup (Fin d) (AryLeavittAlgebra k d)).subtype) ⟨x, hx⟩

/-- **tex 1307, `cor:leavitt-mf-quotient`, proof, last sentence**, every clause:

> So `[H,H] ≤ EL_d(R)`, while `EL_d(R) ≤ [H,H]` because every homomorphism from `EL_d(R)`
> to an MF group is trivial (Theorem `thm:full-defect-ring`).

for every countable field `k` and every `d ≥ 2`, with `R = L_k(1,d)` and `H = GL_d(R)`. -/
def PrintedLeavittBothInclusions : Prop :=
  ∀ (k : Type) [Field k] [Countable k] (d : ℕ), 2 ≤ d →
    commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ ≤
        elementaryGroup (Fin d) (AryLeavittAlgebra k d) ∧
      (∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ (f : elementaryGroup (Fin d) (AryLeavittAlgebra k d) →* M)
          (x : elementaryGroup (Fin d) (AryLeavittAlgebra k d)), f x = 1) ∧
      elementaryGroup (Fin d) (AryLeavittAlgebra k d) ≤
        commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ

/-- **Closed carrier of the sentence.**  The first clause is the closed Khanh--Thanh
consequence, the second is `thm:full-defect-ring` at `L_k(1,d)` and rank `d`, and the third
is the second through `elementary_le_commutator_of_trivial`. -/
theorem manuscriptSentence_bothInclusionsPrinted : PrintedLeavittBothInclusions := by
  intro k _ _ d hd
  have hEL : ∀ (M : Type) [Group M], IsOperatorMF M →
      ∀ (f : elementaryGroup (Fin d) (AryLeavittAlgebra k d) →* M)
        (x : elementaryGroup (Fin d) (AryLeavittAlgebra k d)), f x = 1 :=
    fun M _ hM ↦
      FullDefectRingEJZUnconditional.manuscriptLeavittAlgebraFullDefectRankTwoAllCharacteristics
        k d hd d hd M hM
  exact ⟨KhanhThanhDiagonal.manuscriptSentence_commutatorInElementaryPrinted k d hd, hEL,
    elementary_le_commutator_of_trivial k d hEL⟩

end LeavittMFQuotientBothInclusions
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms
  GroupApproximation.LeavittMFQuotientBothInclusions.manuscriptSentence_bothInclusionsPrinted
#audit_axioms GroupApproximation.LeavittMFQuotientBothInclusions.elementary_le_commutator_of_trivial
