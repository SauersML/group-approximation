import GroupApproximation.BooneHigman.Metabelian.ElemFPK2DilateStColim
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2DilateWire
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₂` dilation from death in the Steinberg group of the pullback

Lane `bh-met-90s`, statement module.  Notation as in `ElemFPK2DilateStRing`:
`P = A ×_L L[X]` with `L = A_s`, and `ι_0 : A[X] → P`, `f ↦ (f(0), λ f)`.

* `k2DilateSt_PullbackDiesAt s`: the hypotheses of `k2Dilate_K2DilatesAt s` (`N ≥ 5`,
  `g ∈ K₂(N, A[X])`, `g(0) = 1`, `λ g` dies after padding), with the conclusion replaced by
  **`ι_0 g` dies after padding in `St(P)`**.
* `k2DilateSt_K2DilatesAt_of_pullback`: the residual gives `k2Dilate_K2DilatesAt s`.  Pad `g`
  to the rank `M` where `ι_0 g` dies, and apply `k2DilateSt_exists_scale_eq_one` (the
  colimit `colim (A[X], μ_s) = P` commutes with `St(M, -)` on elements killed by `ι_0`).
* `k2DilateSt_pullback_of_K2DilatesAt`: the converse.  If `g(s^r X)` dies, then so does
  `ι_0 g = ι_r (g(s^r X))` (cocone `k2DilateSt_toPullback_comp_scale`).
* `Envelope.k2DilateSt_hmClosed_finitelyPresentedMetabelian`: the Boone–Higman root with `hR`
  replaced by the pullback residual `hP : k2DilateSt_PullbackStatement`.

## LOUD: status of the residual

* `k2DilateSt_PullbackDiesAt s` is **equivalent** to `k2Dilate_K2DilatesAt s` for each `A` and
  `s`, by the two proved directions.  It is **strictly smaller in proof content**: the whole
  dilation part (lifting points of `P` to stages, killing the kernel of the stages by
  dilation, and the colimit map `St(P) → ∏_r St(A[X]) / (eventually 1)`) is proved here.  What
  is left mentions no dilation.  It is a Milnor-square statement: `ι_0 g ∈ K₂(P)` has trivial
  images in `St(A)` (`g(0) = 1`) and dies stably in `St(L[X])`, and it should die stably in
  `St(P)`.  This is `K₂` excision for the Milnor square `P = A ×_L L[X]`, restricted to the
  image of `ι_0`.  Excision fails for `K₂` in general, so this restricted case is the actual
  content.
* **Truth**: it follows from `k2Dilate_K2DilatesAt s` (Tulenbaev's lemma) by
  `k2DilateSt_pullback_of_K2DilatesAt`.  For `A = F_p[s_1..s_k][t]`, `A` is regular, so
  Quillen's `NK₂(A) = 0` makes `g` itself die after padding, and then so does `ι_0 g`
  (`k2DilateSt_pullbackDiesAt_of_dies`).
* No citation is a hypothesis.  Nothing is routed through the circular modules listed in the
  brief.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

section DilateStStatement

variable {A : Type*} [CommRing A]

/-- **The pullback residual.**  Take `g ∈ K₂(N, A[X])` with `N ≥ 5` and `g(0) = 1`, and
suppose that `λ g` dies after padding over `A_s[X]`.  Then `ι_0 g` dies after padding over
`P = A ×_{A_s} A_s[X]`. -/
def k2DilateSt_PullbackDiesAt (s : A) : Prop :=
  ∀ N : ℕ, 5 ≤ N → ∀ g : SteinbergGroup (Fin N) (Polynomial A), g ∈ K2 (Fin N) (Polynomial A) →
    SteinbergGroup.ringMap (Polynomial.evalRingHom (0 : A)) g = 1 →
      cubeDiagDilate_StDies
          (SteinbergGroup.ringMap (Polynomial.mapRingHom (algebraMap A (Localization.Away s))) g) →
        cubeDiagDilate_StDies (SteinbergGroup.ringMap (k2DilateSt_toPullback s 0) g)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_PullbackDiesAt

/-- **Reduction**: the pullback residual gives `K₂` dilation. -/
theorem k2DilateSt_K2DilatesAt_of_pullback {s : A} (h : k2DilateSt_PullbackDiesAt s) :
    k2Dilate_K2DilatesAt s := by
  intro N hN g hK hev hloc
  obtain ⟨M, hNM, hM⟩ := h N hN g hK hev hloc
  rw [GroupApproximation.Full.LVStableK2.indexMap_ringMap] at hM
  obtain ⟨m, hm⟩ := k2DilateSt_exists_scale_eq_one (Fin M) s _ hM
  refine ⟨m, M, hNM, ?_⟩
  rw [GroupApproximation.Full.LVStableK2.indexMap_ringMap]
  exact hm m le_rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_K2DilatesAt_of_pullback

/-- The converse: `K₂` dilation gives the pullback residual. -/
theorem k2DilateSt_pullback_of_K2DilatesAt {s : A} (h : k2Dilate_K2DilatesAt s) :
    k2DilateSt_PullbackDiesAt s := by
  intro N hN g hK hev hloc
  obtain ⟨r, hr⟩ := h N hN g hK hev hloc
  have e := k2DilateSt_toPullback_comp_scale s 0 r
  rw [zero_add] at e
  rw [← e, ← SteinbergBasic.ringMap_ringMap]
  exact cubeDiagDilate_stDies_ringMap _ hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_pullback_of_K2DilatesAt

/-- **Truth check**: if every such `g` already dies after padding (as `NK₂(A) = 0` gives), the
pullback residual holds. -/
theorem k2DilateSt_pullbackDiesAt_of_dies {s : A}
    (h : ∀ N : ℕ, 5 ≤ N → ∀ g : SteinbergGroup (Fin N) (Polynomial A),
      g ∈ K2 (Fin N) (Polynomial A) →
        SteinbergGroup.ringMap (Polynomial.evalRingHom (0 : A)) g = 1 → cubeDiagDilate_StDies g) :
    k2DilateSt_PullbackDiesAt s :=
  fun N hN g hK hev _ ↦ cubeDiagDilate_stDies_ringMap _ (h N hN g hK hev)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_pullbackDiesAt_of_dies

end DilateStStatement

section DilateStPoly

/-- **The residual of lane `bh-met-90s`**: the pullback residual for `A = F_p[s_1..s_k][t]`,
`p` prime, and constants `s = C s₀`. -/
def k2DilateSt_PullbackStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (k : ℕ) (s₀ : MvPolynomial (Fin k) (ZMod p)),
    k2DilateSt_PullbackDiesAt (Polynomial.C s₀ : Polynomial (MvPolynomial (Fin k) (ZMod p)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_PullbackStatement

/-- **Endpoint**: `k2Dilate_PolyK2Statement` from the pullback residual. -/
theorem k2DilateSt_polyK2_of_pullback (h : k2DilateSt_PullbackStatement) :
    k2Dilate_PolyK2Statement :=
  fun p hp k s₀ ↦ k2DilateSt_K2DilatesAt_of_pullback (h p hp k s₀)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_polyK2_of_pullback

/-- The converse: the pullback residual from `k2Dilate_PolyK2Statement`. -/
theorem k2DilateSt_pullback_of_polyK2 (h : k2Dilate_PolyK2Statement) :
    k2DilateSt_PullbackStatement :=
  fun p hp k s₀ ↦ k2DilateSt_pullback_of_K2DilatesAt (h p hp k s₀)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_pullback_of_polyK2

/-- The cube gap `hloc` from the local residual and the pullback residual. -/
theorem k2DilateSt_polyK2CubeNilLocal (hL : k2CubeDilate_LocalStatement)
    (hP : k2DilateSt_PullbackStatement) : PolyK2CubeNilLocalStatement :=
  k2Dilate_polyK2CubeNilLocal hL (k2DilateSt_polyK2_of_pullback hP)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_polyK2CubeNilLocal

end DilateStPoly

end GroupApproximation.BooneHigman.Metabelian.ElemFP

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Boone–Higman root, pullback form**: `hloc` is replaced by the local residual `hL` and the
pullback residual `hP`. -/
theorem k2DilateSt_hmClosed_finitelyPresentedMetabelian
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hL : ElemFP.k2CubeDilate_LocalStatement)
    (hP : ElemFP.k2DilateSt_PullbackStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  k2Dilate_hmClosed_finitelyPresentedMetabelian hH hvdk hL
    (ElemFP.k2DilateSt_polyK2_of_pullback hP) hgen hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.k2DilateSt_hmClosed_finitelyPresentedMetabelian

end GroupApproximation.BooneHigman.Metabelian.Envelope
