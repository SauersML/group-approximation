import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PullRelInj
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PullExcStatement
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeDiagDilateSt
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStableK2.Reduction
import GroupApproximation.Meta.AxiomGuard

/-!
# The relative Steinberg action residual

Lane `bh-met-91g`, statement module.  Notation: `P = A ×_L L[X]`, `L = A_s`, and
`K = ker (fst : St(M, P) → St(M, A))`.

* `k2PullRel_ActionAt s`: for every `M₀` there is `M ≥ M₀` with a group `H`, a homomorphism
  `q : K →* H` and an action `α : St(M, L) →* MulAut H`.  They must satisfy the root formulas
  `F1`–`F3`, `Compat`, and `Faithful` (`q y = 1` forces `y` to die after padding).
* `k2PullRel_pullbackDiesAt_of_actionAt`: `ActionAt s → k2DilateSt_PullbackDiesAt s`.  Pad `ι_0 g`
  to a level `M` above both `N` and the level at which `λ g` dies.  Its `fst` is `g(0) = 1`
  and its `snd` is `λ g = 1`, so `k2PullRel_stDies_of_ringMap` applies.
* `k2PullRel_ActionStatement`, and the reductions `k2PullRel_proper_of_action`,
  `k2PullRel_pullback_of_action` and `Envelope.k2PullRel_hmClosed_finitelyPresentedMetabelian`.

**LOUD: this residual is LOGICALLY EQUIVALENT to `k2PullExc_ProperStatement`.  It is NOT strictly
weaker.**  The converse holds informally:
* Canonical witness: `H = {z ∈ St(M, L[X]) : z(0) = 1} / (dying)`, `q y = [snd y]`, and
  `α d = conjugation by C d`.  `F1`–`F3` and `Compat` are Steinberg relations, and `Faithful`
  is exactly `R1`: `fst y = 1` and `snd y` dies imply `y` dies.
* The target implies `R1`.  `σ_k (a, h(X)) = (a, h(X / s^k))` is an automorphism of `P` with
  `ι_k = σ_k ∘ ι_0`, and `P = ⋃_k ι_k(A[X])`.  Every `y` comes from some `A[X]`-level, and the
  preimage lies in `K₂` because `E(A[X]) ↪ E(P) ↪ E(A) × E(L[X])`, `λ` being injective
  (`k2PullExc_algebraMap_injective`).

A residual with an `_of_` reduction to the target cannot be strictly weaker than an equivalent
target.  What is strictly smaller is the **proof content**.  The Lean here discharges:
* relative generation of `K` over the split retraction `fst ∘ const = id`
  (`ElemFPK2PullRelGen`);
* the construction of `Ψ : St(M, L[X]) → H ⋊ St(M, L)` together with every Steinberg relator
  check (`ElemFPK2PullRelPsi`);
* the semidirect gluing `Ψ ∘ snd = inl ∘ q` (`ElemFPK2PullRelInj`);
* all padding and level bookkeeping, and the `K₂` hypothesis, which is unused.
What remains is only to produce `(H, q, α)` with explicit root formulas and faithfulness.  The
choice of `H` trades the construction of `α` against faithfulness.

**Why this is true despite Swan.**  Swan's failure of `K₂` excision is measured by
`I ⊗_P (B / P)` with `I = X L[X] = ker fst`.  Here `s` is a nonzerodivisor on `P`, and
`I = s^n I` is uniquely `s`-divisible.  `B / P = P_s / P` is `s`-power torsion, so the
obstruction vanishes.  `(P → A, P → P_s = L[X])` is a Karoubi (Milnor) square with
`P / s^n ≅ A / s^n`.  This informal argument is not a hypothesis.  No citation is a hypothesis,
and nothing is routed through the circular modules of the brief.
-/

universe u

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

section PullRelStatement

/-- **The relative action residual at `s`.** -/
def k2PullRel_ActionAt {A : Type u} [CommRing A] (s : A) : Prop :=
  ∀ M₀ : ℕ, ∃ M : ℕ, M₀ ≤ M ∧ ∃ (H : Type u) (_ : Group H) (q : k2PullRel_ker s M →* H)
    (α : SteinbergGroup (Fin M) (Localization.Away s) →* MulAut H),
      k2PullRel_Faithful q ∧ k2PullRel_Compat q α ∧ k2PullRel_F1 q α ∧ k2PullRel_F2 q α ∧
        k2PullRel_F3 q α

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_ActionAt

/-- **Reduction**: the relative action residual gives the pullback residual at `s`. -/
theorem k2PullRel_pullbackDiesAt_of_actionAt {A : Type u} [CommRing A] {s : A}
    (h : k2PullRel_ActionAt s) : k2DilateSt_PullbackDiesAt s := by
  intro N _ g _ hg0 hgL
  obtain ⟨M', hNM', hM'⟩ := hgL
  obtain ⟨M, hM, H, _, q, α, hQ, hC, hF1, hF2, hF3⟩ := h (max N M')
  have hNM : N ≤ M := (le_max_left N M').trans hM
  have hM'M : M' ≤ M := (le_max_right N M').trans hM
  refine cubeDiagDilate_stDies_of_indexMap hNM
    (k2PullRel_stDies_of_ringMap q α hF1 hF2 hF3 hC hQ ?_ ?_)
  · rw [← GroupApproximation.Full.LVStableK2.indexMap_ringMap, ringMap_ringMap,
      k2PullRel_fst_comp_toPullback, hg0, map_one]
  · rw [← GroupApproximation.Full.LVStableK2.indexMap_ringMap, ringMap_ringMap,
      k2PullRel_snd_comp_toPullback]
    exact cubeDiagDilate_indexMap_eq_one_of_le hNM' hM'M hNM hM'

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_pullbackDiesAt_of_actionAt

/-- **The relative action residual**, for the proper constants of `k2PullExc_ProperStatement`. -/
def k2PullRel_ActionStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (k : ℕ) (s₀ : MvPolynomial (Fin k) (ZMod p)), s₀ ≠ 0 → ¬ IsUnit s₀ →
    k2PullRel_ActionAt (Polynomial.C s₀ : Polynomial (MvPolynomial (Fin k) (ZMod p)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_ActionStatement

/-- **Reduction**: the relative action residual gives the proper residual. -/
theorem k2PullRel_proper_of_action (h : k2PullRel_ActionStatement) :
    k2PullExc_ProperStatement :=
  fun p hp k s₀ h0 hu ↦ k2PullRel_pullbackDiesAt_of_actionAt (h p hp k s₀ h0 hu)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_proper_of_action

/-- **Reduction**: the relative action residual gives the lane-`90s` pullback residual. -/
theorem k2PullRel_pullback_of_action (h : k2PullRel_ActionStatement) :
    k2DilateSt_PullbackStatement :=
  k2PullExc_pullback_of_proper (k2PullRel_proper_of_action h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_pullback_of_action

end PullRelStatement

end GroupApproximation.BooneHigman.Metabelian.ElemFP

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Boone–Higman root, relative action form**: as
`k2PullExc_hmClosed_finitelyPresentedMetabelian`, with the proper residual replaced by the
relative action residual `hA`. -/
theorem k2PullRel_hmClosed_finitelyPresentedMetabelian
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hL : ElemFP.k2CubeDilate_LocalStatement)
    (hA : ElemFP.k2PullRel_ActionStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  k2PullExc_hmClosed_finitelyPresentedMetabelian hH hvdk hL
    (ElemFP.k2PullRel_proper_of_action hA) hgen hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.k2PullRel_hmClosed_finitelyPresentedMetabelian

end GroupApproximation.BooneHigman.Metabelian.Envelope
