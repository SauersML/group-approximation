import GroupApproximation.CharClass.LIXKGenLocalHomotopy
import GroupApproximation.CharClass.LIXKGenLocalSplitOf
import GroupApproximation.CharClass.RelHomotopyInvariance
import GroupApproximation.CharClass.RelativeLocalModelOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The local computation at each zero, over a field, at rank `n`

Lane `lx-stepcK-local` (LIX strongest swarm, 2026-09-12): the first two fields of
`KGen.KZeroStepCDataOf` over a field `K`, through `KGen.exists_localSplit_ne_zero_kgenOf`.

At `F₂` the local square of Step C is cut twice by the line trick: the comparison homotopy is cut
because the relative group of the chart pair is an `F₂`-line, and the linear far end acts as the
identity for the same reason.  Over a field neither survives, and neither is needed:

* the homotopy is cut by relative homotopy invariance over any ring
  (`RelativeSupport.relPullback_eq_of_contractible_param`);
* the far end is only needed to **reflect nonvanishing**, and its pullback is an isomorphism of
  pairs (`relPairIso`) followed by excision at the origin (`excisionIsoPointOf`), whatever unit it
  multiplies the local generator by.

So the only input is that `u` restricts nontrivially to the fibre over each zero, a property of a
Thom class and of nothing about the section.

The geometry (the chart point, the homotopy, its two ends, the fibre map) carries no coefficients
and is lane `lx-local2a`'s, in `CharClass/LIXKGenLocalHomotopy.lean`.

## Main declarations

* `KGen.restrictTo_relPullback_ne_zero_of_homotopy` — the abstract cut, over any commutative ring.
* `KGen.lixKFarMap_relPullback_ne_zero` — the far end reflects nonvanishing of the fibre class.
* `KGen.kGenLocalNonzeroOf_of_fibre` — **`KGenLocalNonzeroOf K n k … u` from the fibre classes.**
* `KGen.exists_localSplit_ne_zero_kgenOf_of_fibre` — the split with nonzero local classes.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

/-! ## 1. The abstract cut, over any ring -/

/-- **A class survives restriction near a zero if a far end joined to the section sees it.**

`sec` is a map of pairs `(N, C) → (E, S)`, `B ⊆ N`, and `chartPt ≫ sInclusion B ≫ sec` is joined
to `far` by a homotopy of pairs out of `(U, A)` with a contractible parameter space.  If the far
end's pullback of `u` is nonzero, so is the restriction to `B` of the section's pullback. -/
theorem restrictTo_relPullback_ne_zero_of_homotopy (R : Type) [CommRing R]
    {N E : TopCat.{0}} {C : Set N} {S : Set E}
    (sec : N ⟶ E) (hsec : ∀ x ∈ C, (ConcreteCategory.hom sec) x ∈ S)
    (B : Set N) {U : Type} [TopologicalSpace U] {A : Set U}
    (chartPt : TopCat.of U ⟶ TopCat.of ↥B)
    (hchart : ∀ x ∈ A, (ConcreteCategory.hom chartPt) x ∈ (Subtype.val : ↥B → N) ⁻¹' C)
    {P : Type} [TopologicalSpace P] (hP : ContractibleSpace P) (b b' : P)
    (Hm : TopCat.of (P × U) ⟶ E)
    (hHm : ∀ q ∈ {q : P × U | q.2 ∈ A}, (ConcreteCategory.hom Hm) q ∈ S)
    (far : TopCat.of U ⟶ E)
    (hbf : RelativeSupport.sliceMap b U ≫ Hm = chartPt ≫ sInclusion (X := N) B ≫ sec)
    (hbg : RelativeSupport.sliceMap b' U ≫ Hm = far)
    (hfar : ∀ x ∈ A, (ConcreteCategory.hom far) x ∈ S) (q : ℕ)
    (u : relCohomology R E S q) (hu : (relPullback R far hfar q).hom u ≠ 0) :
    (LIXKRelMV.restrictTo R B C q).hom ((relPullback R sec hsec q).hom u) ≠ 0 := by
  have hBS : ∀ y ∈ (Subtype.val : ↥B → N) ⁻¹' C,
      (ConcreteCategory.hom (sInclusion (X := N) B ≫ sec)) y ∈ S :=
    fun y hy => hsec _ hy
  have hL : ∀ x ∈ A,
      (ConcreteCategory.hom (chartPt ≫ sInclusion (X := N) B ≫ sec)) x ∈ S :=
    fun x hx => hBS _ (hchart x hx)
  have hcut : relPullback R (chartPt ≫ sInclusion (X := N) B ≫ sec) hL q
      = relPullback R far hfar q :=
    RelativeSupport.relPullback_eq_of_contractible_param R hP b b' Hm hHm hbf hbg hL hfar q
  have hc1 : relPullback R (chartPt ≫ sInclusion (X := N) B ≫ sec) hL q
      = relPullback R (sInclusion (X := N) B ≫ sec) hBS q ≫ relPullback R chartPt hchart q :=
    relPullback_comp R chartPt (sInclusion (X := N) B ≫ sec) hchart hBS hL q
  have hc2 : relPullback R (sInclusion (X := N) B ≫ sec) hBS q
      = relPullback R sec hsec q ≫ LIXKRelMV.restrictTo R B C q :=
    relPullback_comp R (sInclusion (X := N) B) sec (LIXKRelMV.sInclusion_mapsTo_preimage B C)
      hsec hBS q
  intro h0
  apply hu
  rw [← hcut, hc1, hc2]
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rw [h0, map_zero]

/-! ## 2. The far end reflects nonvanishing -/

theorem lixKFarMap_eq_comp (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    lixKFarMap n k dd i hGc hGu
      = sInclusion (X := TopCat.of (Fin (lixRank n dd) → ℂ)) (lixKU n k dd i hGc hGu)
          ≫ (lixKGMap n k i hGc hGu ≫ cmap (lixKFibreMap n k dd i hGc hGu)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro v
  rfl

/-- **The far end's pullback of `u` is nonzero when the fibre class is**, over any field: the far
end is excision at the origin, a linear automorphism of `ℂ^r`, and the fibre over the zero. -/
theorem lixKFarMap_relPullback_ne_zero (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ)
    (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd))
    (hfib : (relPullback K (cmap (lixKFibreMap n k dd i hGc hGu))
      (lixKFibreMap_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)).hom u ≠ 0) :
    (relPullback K (lixKFarMap n k dd i hGc hGu) (lixKFar_mapsTo n k dd i hGc hGu)
      (2 * lixRank n dd)).hom u ≠ 0 := by
  have hU : ∀ x ∈ ((Subtype.val : ↥(lixKU n k dd i hGc hGu) → (Fin (lixRank n dd) → ℂ)) ⁻¹'
      ({0}ᶜ : Set (Fin (lixRank n dd) → ℂ))),
      (ConcreteCategory.hom (sInclusion (X := TopCat.of (Fin (lixRank n dd) → ℂ))
        (lixKU n k dd i hGc hGu))) x ∈ puncturedSet (lixRank n dd) :=
    fun _ hx => hx
  have hg : ∀ y ∈ puncturedSet (lixRank n dd),
      (ConcreteCategory.hom (lixKGMap n k i hGc hGu ≫ cmap (lixKFibreMap n k dd i hGc hGu))) y
        ∈ lixPuncturedInTotal n hGc hGu :=
    fun y hy => lixKFibreMap_mapsTo n k dd i hGc hGu _ (lixKGHomeo_mapsTo n k i hGc hGu y hy)
  have hfg : ∀ x ∈ ((Subtype.val : ↥(lixKU n k dd i hGc hGu) → (Fin (lixRank n dd) → ℂ)) ⁻¹'
      ({0}ᶜ : Set (Fin (lixRank n dd) → ℂ))),
      (ConcreteCategory.hom (sInclusion (X := TopCat.of (Fin (lixRank n dd) → ℂ))
          (lixKU n k dd i hGc hGu)
        ≫ (lixKGMap n k i hGc hGu ≫ cmap (lixKFibreMap n k dd i hGc hGu)))) x
        ∈ lixPuncturedInTotal n hGc hGu :=
    fun x hx => hg _ (hU x hx)
  have e0 : relPullback K (lixKFarMap n k dd i hGc hGu) (lixKFar_mapsTo n k dd i hGc hGu)
        (2 * lixRank n dd)
      = relPullback K (sInclusion (X := TopCat.of (Fin (lixRank n dd) → ℂ))
          (lixKU n k dd i hGc hGu)
        ≫ (lixKGMap n k i hGc hGu ≫ cmap (lixKFibreMap n k dd i hGc hGu))) hfg
          (2 * lixRank n dd) :=
    relPullback_eq_of_eq K (lixKFarMap_eq_comp n k dd i hGc hGu)
      (lixKFar_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)
  have e1 : relPullback K (sInclusion (X := TopCat.of (Fin (lixRank n dd) → ℂ))
          (lixKU n k dd i hGc hGu)
        ≫ (lixKGMap n k i hGc hGu ≫ cmap (lixKFibreMap n k dd i hGc hGu))) hfg
          (2 * lixRank n dd)
      = relPullback K (lixKGMap n k i hGc hGu ≫ cmap (lixKFibreMap n k dd i hGc hGu)) hg
          (2 * lixRank n dd)
        ≫ relPullback K (sInclusion (X := TopCat.of (Fin (lixRank n dd) → ℂ))
          (lixKU n k dd i hGc hGu)) hU (2 * lixRank n dd) :=
    relPullback_comp K _ _ hU hg hfg (2 * lixRank n dd)
  have e2 : relPullback K (lixKGMap n k i hGc hGu ≫ cmap (lixKFibreMap n k dd i hGc hGu)) hg
        (2 * lixRank n dd)
      = relPullback K (cmap (lixKFibreMap n k dd i hGc hGu))
          (lixKFibreMap_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)
        ≫ relPullback K (lixKGMap n k i hGc hGu) (lixKGHomeo_mapsTo n k i hGc hGu)
          (2 * lixRank n dd) :=
    relPullback_comp K _ _ (lixKGHomeo_mapsTo n k i hGc hGu)
      (lixKFibreMap_mapsTo n k dd i hGc hGu) hg (2 * lixRank n dd)
  have h1 := ne_zero_of_isoOf
    (relPairIso K (lixKGIso n k i hGc hGu) (lixKGHomeo_mapsTo n k i hGc hGu)
      (lixKGHomeo_symm_mapsTo n k i hGc hGu) (2 * lixRank n dd)) hfib
  have h2 := ne_zero_of_isoOf
    (excisionIsoPointOf K (TopCat.of (Fin (lixRank n dd) → ℂ)) 0 (lixKU n k dd i hGc hGu)
      (isOpen_lixKU n k dd i hGc hGu) (zero_mem_lixKU n k dd i hGc hGu) (2 * lixRank n dd)) h1
  rw [e0, e1, e2]
  exact h2

/-! ## 3. The local computation at every zero -/

/-- **The local computation over a field at rank `n`, from the fibre classes.**  For any class `u`
of the bundle pair that restricts nontrivially to the fibre over each zero, the section's pullback
of `u` restricts nontrivially to the neighbourhood `lixKTrivBall` of each zero, which contains no
other zero. -/
theorem kGenLocalNonzeroOf_of_fibre (K : Type) [Field K] (n k : ℕ) {dd : Fin ℓ → ℕ}
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    (u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd))
    (hfib : ∀ i : Fin (k + 1), (relPullback K (cmap (lixKFibreMap n k dd i hGc hGu))
      (lixKFibreMap_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)).hom u ≠ 0) :
    KGenLocalNonzeroOf K n k hGc hGu hGe u := by
  intro i
  refine ⟨lixKTrivBall n k dd i hGc hGu,
    fun j hj => lixKZero_notMem_lixKTrivBall n k dd i hGc hGu j hj, ?_⟩
  exact restrictTo_relPullback_ne_zero_of_homotopy K (lixKS n k hGc hGu hGe)
    (lixKSectionTotal_mapsTo n k hGc hGu hGe) (lixKTrivBall n k dd i hGc hGu)
    (lixKChartPt n k dd i hGc hGu) (lixKChartPt_mapsTo n k dd i hGc hGu)
    contractibleSpace_lixI ⟨(1 : ℝ), Set.right_mem_Icc.mpr zero_le_one⟩
    ⟨(0 : ℝ), Set.left_mem_Icc.mpr zero_le_one⟩
    (cmap (lixKHomotopyFun n k dd i hGc hGu)) (lixKHomotopy_mapsTo n k dd i hGc hGu)
    (lixKFarMap n k dd i hGc hGu) (lixKHomotopy_end_one n k dd i hGc hGu hGe)
    (lixKHomotopy_end_zero n k dd i hGc hGu) (lixKFar_mapsTo n k dd i hGc hGu)
    (2 * lixRank n dd) u (lixKFarMap_relPullback_ne_zero K n k dd i hGc hGu u (hfib i))

/-- **The split, with every local class nonzero, over a field**, from the fibre classes. -/
theorem exists_localSplit_ne_zero_kgenOf_of_fibre (K : Type) [Field K] (n k : ℕ)
    {dd : Fin ℓ → ℕ}
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    (u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd))
    (hfib : ∀ i : Fin (k + 1), (relPullback K (cmap (lixKFibreMap n k dd i hGc hGu))
      (lixKFibreMap_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)).hom u ≠ 0) :
    ∃ xloc : ∀ i : Fin (k + 1), relCohomology K (lixN n dd)
        ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd),
      LocalSplit (fun i => lixKRhoOf K n k dd i (2 * lixRank n dd))
          ((lixKSRelOf K n k hGc hGu hGe (2 * lixRank n dd)).hom u) xloc ∧
        ∀ i, xloc i ≠ 0 :=
  exists_localSplit_ne_zero_kgenOf K n k hGc hGu hGe u
    (kGenLocalNonzeroOf_of_fibre K n k hGc hGu hGe u hfib)

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.restrictTo_relPullback_ne_zero_of_homotopy
#audit_axioms KGen.lixKFarMap_relPullback_ne_zero
#audit_axioms KGen.kGenLocalNonzeroOf_of_fibre
#audit_axioms KGen.exists_localSplit_ne_zero_kgenOf_of_fibre

end GroupApproximation.CharClass
