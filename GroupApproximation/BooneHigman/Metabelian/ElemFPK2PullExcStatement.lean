import Mathlib.Algebra.Field.ZMod
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PullExcDegenerate
import GroupApproximation.Meta.AxiomGuard

/-!
# Pullback excision for `F_p[s_1..s_k][t]`: the proper residual

Lane `bh-met-90z`, statement module.  Lane `bh-met-90s` reduced the `hR` side of the
Boone–Higman root to `k2DilateSt_PullbackStatement`: for `A = F_p[s_1..s_k][t]` and every
constant `s = C s₀`, the pullback residual `k2DilateSt_PullbackDiesAt s` holds.

* `k2PullExc_pullbackDiesAt_C_of_degenerate`: the residual at `C s₀` when `s₀ = 0` (then
  `A_s = 0`) or `s₀` is a unit (then `A → A_s` is an isomorphism).  Both cases are proved in
  `ElemFPK2PullExcDegenerate`, over any commutative ring.
* `k2PullExc_ProperStatement`: the residual only for **proper** `s₀`: `s₀ ≠ 0` and `s₀` not a
  unit.  `k2PullExc_pullback_of_proper` gives `k2DilateSt_PullbackStatement` from it.
* `k2PullExc_algebraMap_injective`: for `s₀ ≠ 0`, `A → A_s` is injective (`A` is a domain), so
  by `k2PullExc_snd_injective` the pullback `P` is the conductor subring
  `{h ∈ A_s[X] : h(0) ∈ A}` of `A_s[X]`, with conductor `X A_s[X]`.
* `Envelope.k2PullExc_hmClosed_finitelyPresentedMetabelian`: the root with `hP` replaced by
  the proper residual.

## LOUD: status of the residual

* `k2PullExc_ProperStatement` is implied by `k2DilateSt_PullbackStatement`
  (`k2PullExc_proper_of_pullback`), and conversely by the proved degenerate cases.  So it is
  **logically equivalent** to the lane-`90s` residual, with **strictly smaller proof content**:
  the cases `s₀ = 0` and `s₀` a unit are closed.  For `k = 0`, `F_p[∅]` is the field `F_p`, so
  every instance of the proper residual with `k = 0` is vacuous; the open content is `k ≥ 1`
  and `s₀` of positive degree.
* **Truth**: it follows from `k2DilateSt_PullbackStatement`, which follows from Tulenbaev's
  dilation lemma (lane `90s`, `k2DilateSt_pullback_of_polyK2`).  It is true.
* **What is left**: for proper `s₀`, `P ⊂ L[X]` (`L = A_s`) with conductor `X L[X]`, and the
  question is whether `ι_0 g ∈ K₂(P)` with `g(0) = 1`, dying stably in `St(L[X])`, dies stably
  in `St(P)`.  This is `K₂` excision for the conductor square restricted to the image of
  `ι_0`.  No relative Steinberg presentation `St(P, X L[X])` is proved here; that is the gap.
* No citation is a hypothesis.  Nothing is routed through the circular modules of the brief.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

section PullExcStatement

/-- **Degenerate constants**: the pullback residual holds at `C s₀` when `s₀ = 0` or `s₀` is a
unit, over any commutative ring. -/
theorem k2PullExc_pullbackDiesAt_C_of_degenerate {R : Type*} [CommRing R] {s₀ : R}
    (h : s₀ = 0 ∨ IsUnit s₀) :
    k2DilateSt_PullbackDiesAt (Polynomial.C s₀ : Polynomial R) := by
  rcases h with h0 | hu
  · rw [h0, Polynomial.C_0]
    exact k2PullExc_pullbackDiesAt_zero
  · exact k2PullExc_pullbackDiesAt_of_isUnit (hu.map (Polynomial.C : R →+* Polynomial R))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullExc_pullbackDiesAt_C_of_degenerate

/-- **The proper residual**: the pullback residual for `A = F_p[s_1..s_k][t]`, `p` prime, and
constants `s = C s₀` with `s₀ ≠ 0` and `s₀` not a unit. -/
def k2PullExc_ProperStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (k : ℕ) (s₀ : MvPolynomial (Fin k) (ZMod p)), s₀ ≠ 0 → ¬ IsUnit s₀ →
    k2DilateSt_PullbackDiesAt (Polynomial.C s₀ : Polynomial (MvPolynomial (Fin k) (ZMod p)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullExc_ProperStatement

/-- **Reduction**: the proper residual gives the lane-`90s` pullback residual. -/
theorem k2PullExc_pullback_of_proper (h : k2PullExc_ProperStatement) :
    k2DilateSt_PullbackStatement := by
  intro p hp k s₀
  by_cases h0 : s₀ = 0
  · exact k2PullExc_pullbackDiesAt_C_of_degenerate (Or.inl h0)
  by_cases hu : IsUnit s₀
  · exact k2PullExc_pullbackDiesAt_C_of_degenerate (Or.inr hu)
  exact h p hp k s₀ h0 hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullExc_pullback_of_proper

/-- The converse (so the two residuals are equivalent). -/
theorem k2PullExc_proper_of_pullback (h : k2DilateSt_PullbackStatement) :
    k2PullExc_ProperStatement :=
  fun p hp k s₀ _ _ ↦ h p hp k s₀

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullExc_proper_of_pullback

/-- **Domain case**: for `s₀ ≠ 0`, `A → A_{C s₀}` is injective, since `A = F_p[s_1..s_k][t]` is
a domain. -/
theorem k2PullExc_algebraMap_injective {p : ℕ} (hp : p.Prime) {k : ℕ}
    {s₀ : MvPolynomial (Fin k) (ZMod p)} (h0 : s₀ ≠ 0) :
    Function.Injective (algebraMap (Polynomial (MvPolynomial (Fin k) (ZMod p)))
      (Localization.Away (Polynomial.C s₀ : Polynomial (MvPolynomial (Fin k) (ZMod p))))) := by
  haveI := Fact.mk hp
  exact IsLocalization.injective _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (Polynomial.C_ne_zero.2 h0))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullExc_algebraMap_injective

end PullExcStatement

end GroupApproximation.BooneHigman.Metabelian.ElemFP

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Boone–Higman root, proper pullback form**: as
`k2DilateSt_hmClosed_finitelyPresentedMetabelian`, with the pullback residual replaced by the
proper residual `hP` (constants `s₀ ≠ 0` that are not units). -/
theorem k2PullExc_hmClosed_finitelyPresentedMetabelian
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hL : ElemFP.k2CubeDilate_LocalStatement)
    (hP : ElemFP.k2PullExc_ProperStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  k2DilateSt_hmClosed_finitelyPresentedMetabelian hH hvdk hL
    (ElemFP.k2PullExc_pullback_of_proper hP) hgen hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.k2PullExc_hmClosed_finitelyPresentedMetabelian

end GroupApproximation.BooneHigman.Metabelian.Envelope
