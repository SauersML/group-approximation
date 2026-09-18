import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroRankFourFPReduce
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroSLFourFPIntIso
import GroupApproximation.BooneHigman.SteinbergBasic.Kernel
import GroupApproximation.Steinberg.Functoriality
import Mathlib.RingTheory.Localization.Away.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# `SL_4(ℤ[1/m])` f.p. from the Steinberg half and the `K₂` half (bh-met-91f)

Target: `czRankFourFP_SLFourStatement` (`SL_4(ℤ[1/m])` is finitely presented for `m ≥ 1`).

**Proved here.**
* `czSLFourFP_sl_of_st_of_k2Fng`: if `St_4(ℤ[1/m])` is finitely presented
  (`czSLFourFP_StFourStatement`) and `K₂(4, ℤ[1/m])` is finitely normally generated
  (the corpus interface `CZK2FngRankFourStatement`), then the target holds.  Proof: `E_4` is
  the quotient of `St_4` by `K₂`, then `SL_4 ≃* E_4` (`czRankFourFP_slEquiv`).
* `czSLFourFP_k2Fng_iff_sl_of_st`: given the Steinberg half, the `K₂` half is **equivalent** to
  the target (the converse is `czRankFourFP_k2FngRankFour_of_sl`).
* `czSLFourFP_stFour_one`: the Steinberg half at `m = 1`, outright, from the finite
  presentation of `St_I(ℤ)` (`czSLFourFP_stInt_isFinitelyPresented`, proved in
  `ElemFPCharZeroSLFourFPIntIso` with no rank hypothesis and no literature input).

**Residual (LOUD).**  The Steinberg half `czSLFourFP_StFourStatement` for `m > 1` is not
closed.  It is strictly smaller in proof content than the target, since it carries no `K₂`
information, and it is closed here at `m = 1`.  The second input `CZK2FngRankFourStatement` is
pre-existing, and given the Steinberg half it is only **equivalent** to the target.  So this
file splits the target into two halves and closes neither for `m > 1`.

**Truth check.**  `St_4(ℤ[1/m])` is finitely presented.  It is a central extension of the
finitely presented `E_4(ℤ[1/m]) = SL_4(ℤ[1/m])` by the finitely generated abelian group
`K₂(4, ℤ[1/m])`.  This is used for truth only and is not a hypothesis anywhere.  No unit-symbol
route, no Swan–Weibel dilation and no circular Higman interface is used.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **The Steinberg half.**  `St_4(ℤ[1/m])` is finitely presented for `m ≥ 1`.  True (see the
module docstring); proved here for `m = 1` (`czSLFourFP_stFour_one`). -/
def czSLFourFP_StFourStatement : Prop :=
  ∀ m : ℕ, 0 < m →
    Group.IsFinitelyPresented (SteinbergGroup (Fin 4) (Localization.Away (m : ℤ)))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_StFourStatement

/-- **Reduction.**  The Steinberg half and the `K₂` half give `SL_4(ℤ[1/m])` f.p. -/
theorem czSLFourFP_sl_of_st_of_k2Fng (hst : czSLFourFP_StFourStatement)
    (hk : CZK2FngRankFourStatement) : czRankFourFP_SLFourStatement := by
  intro m hm
  haveI := hst m hm
  haveI : Group.IsFinitelyPresented (elementaryGroup (Fin 4) (Localization.Away (m : ℤ))) :=
    isFinitelyPresented_elementaryGroup_of (hk m hm)
  exact Group.IsFinitelyPresented.equiv (czRankFourFP_slEquiv m (N := 4) (by omega)).symm

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_sl_of_st_of_k2Fng

/-- **Strength (LOUD).**  Given the Steinberg half, the `K₂` half is equivalent to the target. -/
theorem czSLFourFP_k2Fng_iff_sl_of_st (hst : czSLFourFP_StFourStatement) :
    CZK2FngRankFourStatement ↔ czRankFourFP_SLFourStatement :=
  ⟨czSLFourFP_sl_of_st_of_k2Fng hst, czRankFourFP_k2FngRankFour_of_sl⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_k2Fng_iff_sl_of_st

/-- **The Steinberg half at `m = 1`.**  `ℤ[1/1] ≃+* ℤ` and `St_4(ℤ)` is finitely presented. -/
theorem czSLFourFP_stFour_one :
    Group.IsFinitelyPresented (SteinbergGroup (Fin 4) (Localization.Away ((1 : ℕ) : ℤ))) :=
  haveI := czSLFourFP_stInt_isFinitelyPresented (Fin 4)
  Group.IsFinitelyPresented.equiv (SteinbergGroup.coefficientEquiv (I := Fin 4)
    (IsLocalization.atUnit ℤ (Localization.Away ((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ)
      (by rw [Nat.cast_one]; exact isUnit_one)).toRingEquiv)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czSLFourFP_stFour_one

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
