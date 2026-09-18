import Mathlib.Algebra.Field.ZMod
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PullActQuot
import GroupApproximation.Meta.AxiomGuard

/-!
# The relative action residual: the case `k = 0`, and the positive residual

Lane `bh-met-91s`, statement module.  Target: `k2PullRel_ActionStatement` (lane `bh-met-91g`).

## Truth check

* The target is **true**.  It is equivalent to `k2PullExc_ProperStatement` (lane `91g`
  docstring): the canonical witness `H = ker (ev₀ : St(M, L[X]) → St(M, L)) ⧸ (dying)`,
  `q y = [snd y]`, `α d = conjugation by C d` satisfies `F1`–`F3` and `Compat` by Steinberg
  relations, and its faithfulness is `R1` (`fst y = 1`, `snd y` dies ⇒ `y` dies).  `R1` holds for
  `A = F_p[s_1..s_k][t]`: `A` is regular, and the Karoubi square `P → A`, `P → P_s = L[X]`
  (`s` a nonzerodivisor, `P / s^n = A / s^n` because `X L[X]` is `s`-divisible) has a
  Mayer–Vietoris sequence in which `K₃(L[X]) → K₃(L)` is split surjective, so
  `K₂(P) → K₂(A) × K₂(L[X])` is injective.  This informal argument is not a hypothesis.
* A non-circular closure needs the Karoubi/relative-Steinberg content at the Steinberg level;
  it is **not** achieved here.

## What is proved

* `k2PullAct_isUnit_fin_zero`: in `F_p[∅] = F_p` every nonzero element is a unit.  Hence every
  `k = 0` instance of the target is vacuous, and it is closed here (previously only remarked,
  not formalized, in the lane-`90z` docstring).
* `k2PullAct_PosStatement`: the target restricted to `k ≥ 1`.
* `k2PullAct_action_of_pos`: `k2PullAct_PosStatement → k2PullRel_ActionStatement`.
* `k2PullAct_pos_of_action`: the converse.
* `Envelope.k2PullAct_hmClosed_finitelyPresentedMetabelian`: the Boone–Higman root with the
  action residual replaced by the positive residual.
* In `ElemFPK2PullActQuot`: the quotient witness `K ⧸ die` with **unconditional**
  faithfulness, and the reduction `k2PullAct_actionAt_of_quot` (infrastructure only).

## LOUD: status of the remaining gap

`k2PullAct_PosStatement` is **LOGICALLY EQUIVALENT** to `k2PullRel_ActionStatement` (both
directions are proved below), hence to `k2PullExc_ProperStatement`.  It is **NOT strictly
weaker**.  It is strictly smaller in proof content only by the closed `k = 0` case.  It is true
(truth check above).  No citation is a hypothesis; nothing is routed through
`k2DilateSt_PullbackStatement`, `k2PullExc_*` or any dilation hypothesis.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

section PullActStatement

/-- In `F_p[∅] = F_p`, every nonzero element is a unit. -/
theorem k2PullAct_isUnit_fin_zero {p : ℕ} (hp : p.Prime)
    {s₀ : MvPolynomial (Fin 0) (ZMod p)} (h0 : s₀ ≠ 0) : IsUnit s₀ := by
  haveI := Fact.mk hp
  have e := MvPolynomial.eq_C_of_isEmpty s₀
  have hc : s₀.coeff 0 ≠ 0 := by
    intro hc
    apply h0
    rw [e, hc, map_zero]
  rw [e]
  exact (Ne.isUnit hc).map MvPolynomial.C

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullAct_isUnit_fin_zero

/-- **The positive residual**: the relative action residual for `k ≥ 1`. -/
def k2PullAct_PosStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → ∀ s₀ : MvPolynomial (Fin k) (ZMod p),
    s₀ ≠ 0 → ¬ IsUnit s₀ →
      k2PullRel_ActionAt (Polynomial.C s₀ : Polynomial (MvPolynomial (Fin k) (ZMod p)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullAct_PosStatement

/-- **Reduction**: the positive residual gives the relative action residual; the case `k = 0`
is vacuous. -/
theorem k2PullAct_action_of_pos (h : k2PullAct_PosStatement) : k2PullRel_ActionStatement := by
  intro p hp k s₀ h0 hu
  by_cases hk : k = 0
  · subst hk
    exact absurd (k2PullAct_isUnit_fin_zero hp h0) hu
  · exact h p hp k (Nat.one_le_iff_ne_zero.mpr hk) s₀ h0 hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullAct_action_of_pos

/-- The converse (so the two residuals are equivalent). -/
theorem k2PullAct_pos_of_action (h : k2PullRel_ActionStatement) : k2PullAct_PosStatement :=
  fun p hp k _ s₀ h0 hu ↦ h p hp k s₀ h0 hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullAct_pos_of_action

end PullActStatement

end GroupApproximation.BooneHigman.Metabelian.ElemFP

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Boone–Higman root, positive action form**: as
`k2PullRel_hmClosed_finitelyPresentedMetabelian`, with the action residual replaced by the
positive residual `hA` (`k ≥ 1`). -/
theorem k2PullAct_hmClosed_finitelyPresentedMetabelian
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hL : ElemFP.k2CubeDilate_LocalStatement)
    (hA : ElemFP.k2PullAct_PosStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  k2PullRel_hmClosed_finitelyPresentedMetabelian hH hvdk hL
    (ElemFP.k2PullAct_action_of_pos hA) hgen hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.k2PullAct_hmClosed_finitelyPresentedMetabelian

end GroupApproximation.BooneHigman.Metabelian.Envelope
