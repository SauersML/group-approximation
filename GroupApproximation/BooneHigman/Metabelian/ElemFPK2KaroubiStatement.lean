import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KaroubiRing
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KaroubiWitness
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PullActStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# The Karoubi-square injectivity residual `R1`

Lane `bh-met-91v`, statement module.  Target: `k2PullAct_PosStatement` (lane `bh-met-91s`).
Notation: `P = A ×_L L[X]`, `L = A_s`.

* `k2Karoubi_InjAt s` (**`R1`**): for every `M` and `y ∈ St(M, P)`, if `fst y = 1` in
  `St(M, A)` and `snd y = 1` in `St(M, L[X])`, then `y` dies after padding.
* `k2Karoubi_actionAt_of_injAt`: `R1 → k2PullRel_ActionAt s`.  The witness is the canonical
  one of `ElemFPK2KaroubiWitness`: `H = ker ev₀ ⊆ St(M, L[X])`, `q = snd`, `α = conj ∘ C`.
  `F1`–`F3` and `Compat` are proved unconditionally there, and faithfulness is `R1`.
* `k2Karoubi_injAt_of_actionAt`: the converse (pad, then `k2PullRel_stDies_of_ringMap`).
* `k2Karoubi_PosStatement`, `k2Karoubi_actPos_of_pos`, `k2Karoubi_pos_of_actPos`, and
  `Envelope.k2Karoubi_hmClosed_finitelyPresentedMetabelian`.

## Truth check

`R1` is **true** for the relevant `A = F_p[s_1..s_k][t]`, `s = C s₀`.  Informally:
`(P → A, P → P_s = L[X])` is a Karoubi square, with `s` regular on `P`
(`k2Karoubi_const_regular`), `P_s = L[X]` (`k2Karoubi_snd_surj`) and
`s^N P = fst⁻¹ (s^N A)`, so `P / s^N ≅ A / s^N` (`k2Karoubi_span_const_pow`).
`K₃(L[X]) → K₃(L)` is split surjective, so `K₂(P) → K₂(A) × K₂(L[X])` is injective.  This
informal argument is not a hypothesis, and no citation is used.

**LOUD correction to the brief**: "`s^N P = s^N A` as non-unital rings" is **FALSE**
(`k2Karoubi_not_injective_on_dvd`: `lift X ∈ s^N P` is nonzero with `fst = 0`).  The excision
step of the suggested route must use `s^N P = fst⁻¹ (s^N A)` instead.

## LOUD: status of the remaining gap

`k2Karoubi_PosStatement` is **LOGICALLY EQUIVALENT** to `k2PullAct_PosStatement` (both
directions are proved below), hence to `k2PullRel_ActionStatement` and
`k2PullExc_ProperStatement`.  It is **NOT strictly weaker**.  It is strictly smaller only in
proof content: the whole action layer (`H`, `q`, `α`, `F1`–`F3`, `Compat`) is discharged, and
what remains is exactly Steinberg-level `K₂` injectivity for the Karoubi square.  Nothing is
routed through `k2DilateSt_PullbackStatement`, `k2PullExc_*` or any dilation hypothesis.
-/

universe u

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

section KaroubiStatement

/-- **`R1` at `s`**: an element of `St(M, P)` trivial in `St(M, A)` and in `St(M, L[X])` dies
after padding. -/
def k2Karoubi_InjAt {A : Type u} [CommRing A] (s : A) : Prop :=
  ∀ (M : ℕ) (y : SteinbergGroup (Fin M) (k2DilateSt_pullback s)),
    ringMap (k2PullRel_fst s) y = 1 → ringMap (k2PullRel_snd s) y = 1 →
      cubeDiagDilate_StDies y

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_InjAt

/-- **Reduction**: `R1` gives the relative action residual, via the canonical witness. -/
theorem k2Karoubi_actionAt_of_injAt {A : Type u} [CommRing A] {s : A}
    (h : k2Karoubi_InjAt s) : k2PullRel_ActionAt s := fun M₀ ↦
  ⟨M₀, le_rfl, k2Karoubi_kerB s M₀, inferInstance, k2Karoubi_q s M₀, k2Karoubi_alpha s M₀,
    k2Karoubi_faithful_of_inj (h M₀), k2Karoubi_Compat, k2Karoubi_F1, k2Karoubi_F2,
    k2Karoubi_F3⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_actionAt_of_injAt

/-- The converse: the relative action residual gives `R1`. -/
theorem k2Karoubi_injAt_of_actionAt {A : Type u} [CommRing A] {s : A}
    (h : k2PullRel_ActionAt s) : k2Karoubi_InjAt s := by
  intro N y h₁ h₂
  obtain ⟨M, hNM, H, _, q, α, hQ, hC, hF1, hF2, hF3⟩ := h N
  refine cubeDiagDilate_stDies_of_indexMap hNM
    (k2PullRel_stDies_of_ringMap q α hF1 hF2 hF3 hC hQ ?_ ?_)
  · rw [← GroupApproximation.Full.LVStableK2.indexMap_ringMap, h₁, map_one]
  · rw [← GroupApproximation.Full.LVStableK2.indexMap_ringMap, h₂, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_injAt_of_actionAt

/-- **The Karoubi residual**: `R1` for the proper constants with `k ≥ 1`. -/
def k2Karoubi_PosStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → ∀ s₀ : MvPolynomial (Fin k) (ZMod p),
    s₀ ≠ 0 → ¬ IsUnit s₀ →
      k2Karoubi_InjAt (Polynomial.C s₀ : Polynomial (MvPolynomial (Fin k) (ZMod p)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_PosStatement

/-- **Reduction**: the Karoubi residual gives the positive action residual. -/
theorem k2Karoubi_actPos_of_pos (h : k2Karoubi_PosStatement) : k2PullAct_PosStatement :=
  fun p hp k hk s₀ h0 hu ↦ k2Karoubi_actionAt_of_injAt (h p hp k hk s₀ h0 hu)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_actPos_of_pos

/-- The converse (so the two residuals are equivalent). -/
theorem k2Karoubi_pos_of_actPos (h : k2PullAct_PosStatement) : k2Karoubi_PosStatement :=
  fun p hp k hk s₀ h0 hu ↦ k2Karoubi_injAt_of_actionAt (h p hp k hk s₀ h0 hu)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_pos_of_actPos

/-- **Reduction**: the Karoubi residual gives the relative action residual. -/
theorem k2Karoubi_action_of_pos (h : k2Karoubi_PosStatement) : k2PullRel_ActionStatement :=
  k2PullAct_action_of_pos (k2Karoubi_actPos_of_pos h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Karoubi_action_of_pos

end KaroubiStatement

end GroupApproximation.BooneHigman.Metabelian.ElemFP

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Boone–Higman root, Karoubi form**: as `k2PullAct_hmClosed_finitelyPresentedMetabelian`,
with the positive action residual replaced by the Karoubi residual `hK` (`R1`). -/
theorem k2Karoubi_hmClosed_finitelyPresentedMetabelian
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hL : ElemFP.k2CubeDilate_LocalStatement)
    (hK : ElemFP.k2Karoubi_PosStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  k2PullAct_hmClosed_finitelyPresentedMetabelian hH hvdk hL
    (ElemFP.k2Karoubi_actPos_of_pos hK) hgen hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.k2Karoubi_hmClosed_finitelyPresentedMetabelian

end GroupApproximation.BooneHigman.Metabelian.Envelope
