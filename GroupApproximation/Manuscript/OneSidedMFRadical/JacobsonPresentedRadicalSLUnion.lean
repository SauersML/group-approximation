import GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonPresentedSentences
import GroupApproximation.Algebra.FinitaryLinearBinarySLUnion
import GroupApproximation.Meta.AxiomGuard

/-!
# `Rad_MF(EL_n(J)) ≅ ⋃_N SL_N(F_2)` for the presented Toeplitz--Jacobson algebra

`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring` (tex lines 1152--1159 at
origin/main 61363f1b9):

> So `EL_n(J,JeJ)` is this kernel; the quotient `EL_n(F_2[z,z^{-1}])` is residually finite, so
> MF, and `Rad_MF(EL_n(J)) = EL_n(J,JeJ) ≅ ⋃_N SL_N(F_2)` `(n ≥ 4)`, an infinite simple locally
> finite group.

`JacobsonSymbol.manuscriptSentence_jacobsonRadical` states this sentence for the operator model
`jacobsonAlgebra`.  `JacobsonPresented.manuscriptSentence_toeplitzJacobsonRadicalEquality` states
only the equality for the presented algebra.  This module states the whole sentence for
`J = F_2⟨s,t | ts=1⟩` itself.

The isomorphism is built from three steps:
* the equality `Rad_MF(EL_n(J)) = EL_n(J,JeJ)` (`presMfHomKernel_eq`);
* the injective action `presBlockAct n` of `EL_n(J)` on `V^n`, which carries `EL_n(J,JeJ)` onto
  `GL_fs(V^n)` (`presMap_relativeElementary_eq`);
* `GL_fs(V^n) ≅ ⋃_N SL_N(F_2)` (`FinitaryLinear.binaryGLfsEquivSLUnion`).
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace JacobsonPresented

open TorsionComplementaryIdempotents JacobsonSymbol FinitaryLinear JacobsonLaurent

noncomputable section

/-- **`Rad_MF(EL_n(J)) ≅ ⋃_N SL_N(F_2)`** for the presented `J` and `n ≥ 4`. -/
def presRadicalEquivSLUnion (n : ℕ) (hn : 4 ≤ n) :
    MFQuotientUnits.mfHomKernel (elementaryGroup (Fin n) ToeplitzJacobson) ≃* binarySLUnion :=
  haveI : NeZero n := ⟨by omega⟩
  (MulEquiv.subgroupCongr (presMfHomKernel_eq n hn)).trans
    (((relativeElementary (Fin n) presDefectIdeal).equivMapOfInjective (presBlockAct n)
        (presBlockAct_injective n)).trans
      ((MulEquiv.subgroupCongr (presMap_relativeElementary_eq n (by omega))).trans
        (binaryGLfsEquivSLUnion n)))

/-- **Printed (tex 1152--1159), for the presented `J = F_2⟨s,t | ts=1⟩`.**  For `n ≥ 4`, the
reduction `EL_n(J) → EL_n(F_2[z,z^{-1}])` has kernel `EL_n(J,JeJ)`; its target is residually
finite and MF; `Rad_MF(EL_n(J)) = EL_n(J,JeJ)`, and this radical is isomorphic to
`⋃_N SL_N(F_2)`, an infinite simple locally finite group. -/
def PrintedToeplitzJacobsonRadicalSLUnion : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    (presSymbolMap n).ker =
        relativeElementary (Fin n) (TwoSidedIdeal.span {(1 : ToeplitzJacobson) - presS * presT}) ∧
      Group.ResiduallyFinite (elementaryGroup (Fin n) BinaryLaurent) ∧
      IsOperatorMF (elementaryGroup (Fin n) BinaryLaurent) ∧
      MFQuotientUnits.mfHomKernel (elementaryGroup (Fin n) ToeplitzJacobson) =
        relativeElementary (Fin n) (TwoSidedIdeal.span {(1 : ToeplitzJacobson) - presS * presT}) ∧
      Nonempty (MFQuotientUnits.mfHomKernel (elementaryGroup (Fin n) ToeplitzJacobson) ≃*
        binarySLUnion) ∧
      Infinite binarySLUnion ∧ IsSimpleGroup binarySLUnion ∧ IsLocallyFiniteGroup binarySLUnion

/-- Closed proof of the printed sentence for the presented algebra. -/
theorem manuscriptSentence_toeplitzJacobsonRadicalSLUnion :
    PrintedToeplitzJacobsonRadicalSLUnion := by
  intro n hn
  obtain ⟨_, hinf, hsimple, hlf⟩ := manuscriptSentence_binarySLUnionInfiniteSimpleLocallyFinite
  obtain ⟨hrf, hmf⟩ := manuscriptSentence_laurentElementaryResiduallyFiniteMF n
  exact ⟨presKer_eq n (by omega), hrf, hmf, presMfHomKernel_eq n hn,
    ⟨presRadicalEquivSLUnion n hn⟩, hinf, hsimple, hlf⟩

end

end JacobsonPresented
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.OneSidedMFRadical.JacobsonPresented.manuscriptSentence_toeplitzJacobsonRadicalSLUnion
