import GroupApproximation.CharClass.LIXKGenLocalSquare
import GroupApproximation.CharClass.LIXKGenStepCHalfTop
import GroupApproximation.Meta.AxiomGuard

/-!
# The local data of the `k`-zero Step C at rank `n` and `p = 2`, as a theorem

Lane `lx-local2b`.

`KGen.KZeroLocalData n k dd hGc hGu hGe` (`CharClass/LIXKGenStepCHalfTop.lean`) is all that
remained of the Step C half at `p = 2`: local classes at the `k + 1` zeros that split the section
pullback of the Thom class, all nonzero.  The split exists for every class
(`exists_localSplit_kgen`), and a piece is nonzero as soon as the class restricts nontrivially to a
set containing its zero and no other (`exists_localSplit_ne_zero_kgen`).  So the statement to prove
is `KGenLocalNonzero n k hGc hGu hGe (lixThomClassTerm n hGc hGu)`.

The set is `lixKTrivBall n k dd i`.  Restricted there and pulled back to `lixKU`, the class is the
left leg of the compatibility square (`relPullback_lixKGL_chain`).  By the square it equals the
right leg, which is the shrink of the excision at the origin of
`lixKLocalPairIsoClosed (lixKRes u)` (`relPullback_lixKGR_chain`).  That class is nonzero
(`lixKLocalPairIsoClosed_lixKRes_ne_zero`), the excision is an isomorphism, and the shrink is
injective (`injective_lixKShrink`).

## Main results

* `KGen.lixKRestrict_lixThomClassTerm_ne_zero` — the Thom class restricts nontrivially near `z_i`.
* `KGen.kGenLocalNonzero_lixThomClassTerm` — **`KGenLocalNonzero` at the Thom class.**
* `KGen.kZeroLocalData_holds` — **`KZeroLocalData n k dd hGc hGu hGe`, for every `n k dd G`.**
* `KGen.kZeroLocalData_powers` — the `hloc` binder of `Gen.lemmaTwoFor_powers_two_lixChernOf`.
* `KGen.stepCHalf_two_powers_lixChernOf_holds` — the Step C half at `p = 2`, unconditional.
* `KGen.printedKZeroLocalData` — the closed endpoint.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open scoped Matrix
open Set CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

/-- **The Thom class restricts nontrivially to the neighbourhood of the `i`-th zero.** -/
theorem lixKRestrict_lixThomClassTerm_ne_zero (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) :
    (LIXKRelMV.restrictTo (ZMod 2) (X := lixN n dd) (lixKTrivBall n k dd i hGc hGu)
        ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd)).hom
      ((lixKSRel n k hGc hGu hGe (2 * lixRank n dd)).hom (lixThomClassTerm n hGc hGu)) ≠ 0 := by
  intro h0
  have hEq := relPullback_lixKGL_eq_lixKGR n k dd i hGc hGu hGe
  rw [relPullback_lixKGL_chain n k dd i hGc hGu hGe, relPullback_lixKGR_chain n k dd i hGc hGu,
    ← lixKRes_eq n k dd i hGc hGu, ← lixKBundlePairIso_hom_eq n k dd i hGc hGu,
    ← lixKProdIso_hom_eq n k dd i hGc hGu, ← lixKExcF_hom_eq n k dd i] at hEq
  have hL := congrArg (fun f => f.hom (lixThomClassTerm n hGc hGu)) hEq
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hL
  rw [h0, map_zero] at hL
  have hx : (excisionIsoPoint (TopCat.of (Fin (lixRank n dd) → ℂ))
      (0 : Fin (lixRank n dd) → ℂ) (lixKFC n k dd i).target (lixKFC n k dd i).open_target
      (zero_mem_lixKFC_target n k dd i) (2 * lixRank n dd)).hom.hom
        ((lixKLocalPairIsoClosed n k dd i hGc hGu).hom.hom
          ((lixKRes n k dd i hGc hGu (2 * lixRank n dd)).hom (lixThomClassTerm n hGc hGu))) = 0 := by
    apply injective_lixKShrink n k dd i hGc hGu
    rw [map_zero, lixKLocalPairIsoClosed_hom_eq n k dd i hGc hGu]
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    exact hL.symm
  apply lixKLocalPairIsoClosed_lixKRes_ne_zero n k dd i hGc hGu
  rw [← iso_inv_hom_apply (excisionIsoPoint (TopCat.of (Fin (lixRank n dd) → ℂ))
      (0 : Fin (lixRank n dd) → ℂ) (lixKFC n k dd i).target (lixKFC n k dd i).open_target
      (zero_mem_lixKFC_target n k dd i) (2 * lixRank n dd))
    ((lixKLocalPairIsoClosed n k dd i hGc hGu).hom.hom
      ((lixKRes n k dd i hGc hGu (2 * lixRank n dd)).hom (lixThomClassTerm n hGc hGu))), hx,
    map_zero]

/-- **`KGenLocalNonzero` at the Thom class**, with the neighbourhood `lixKTrivBall` at each zero. -/
theorem kGenLocalNonzero_lixThomClassTerm (n k : ℕ) {dd : Fin ℓ → ℕ}
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) :
    KGenLocalNonzero n k hGc hGu hGe (lixThomClassTerm n hGc hGu) := fun i =>
  ⟨lixKTrivBall n k dd i hGc hGu, fun j hj => lixKZero_notMem_lixKTrivBall n k dd i hGc hGu j hj,
    lixKRestrict_lixThomClassTerm_ne_zero n k dd i hGc hGu hGe⟩

/-- **The local data of the `k`-zero Step C, for every rank, exponent, stage and field.** -/
theorem kZeroLocalData_holds (n k : ℕ) (dd : Fin ℓ → ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) :
    KZeroLocalData n k dd hGc hGu hGe :=
  exists_localSplit_ne_zero_kgen n k hGc hGu hGe _ (kGenLocalNonzero_lixThomClassTerm n k hGc hGu hGe)

/-- **The `hloc` binder of `Gen.lemmaTwoFor_powers_two_lixChernOf`**, verbatim. -/
theorem kZeroLocalData_powers (n : ℕ) :
    ∀ (e : ℕ), Odd e → ∀ (j : ℕ) (G : Gen.baseM n (LIX.Gen.lixDD n j) →
        Matrix (Gen.VIdx n (LIX.Gen.lixDD n j)) (Gen.VIdx n (LIX.Gen.lixDD n j)) ℂ)
      (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
      (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n (e - 1) m) 0),
      KZeroLocalData n (e - 1) (LIX.Gen.lixDD n j) hGc hGu hGe :=
  fun e _ j _ hGc hGu hGe => kZeroLocalData_holds n (e - 1) (LIX.Gen.lixDD n j) hGc hGu hGe

/-- **The Step C half at `p = 2`**, at every stage `j` and every odd exponent `e`, with no data. -/
theorem stepCHalf_two_powers_lixChernOf_holds (n : ℕ) [NeZero n] (e : ℕ) (he : Odd e) (j : ℕ) :
    Gen.StepCHalf n (LIX.Gen.lixDD n j) (bVecK n (e - 1))
      (fun W => lixChernOf n (lixChern n (LIX.Gen.lixDD n j)) W
        ((∑ i, LIX.Gen.lixDD n j i) + (n + 1))) :=
  stepCHalf_two_powers_lixChernOf n e he j fun _ hGc hGu hGe =>
    kZeroLocalData_holds n (e - 1) (LIX.Gen.lixDD n j) hGc hGu hGe

/-- The closed form of `kZeroLocalData_holds`. -/
def PrintedKZeroLocalData : Prop :=
  ∀ (n k l : ℕ) (dd : Fin l → ℕ)
    (G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0),
    KZeroLocalData n k dd hGc hGu hGe

theorem printedKZeroLocalData : PrintedKZeroLocalData := by
  intro n k l dd G hGc hGu hGe
  exact kZeroLocalData_holds n k dd hGc hGu hGe

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.lixKRestrict_lixThomClassTerm_ne_zero
#audit_axioms KGen.kGenLocalNonzero_lixThomClassTerm
#audit_axioms KGen.kZeroLocalData_holds
#audit_axioms KGen.kZeroLocalData_powers
#audit_axioms KGen.stepCHalf_two_powers_lixChernOf_holds
#audit_closed_axioms KGen.printedKZeroLocalData

end GroupApproximation.CharClass
