import GroupApproximation.CharClass.LIXKGenOfModel
import GroupApproximation.CharClass.LIXKGenOfBundle
import GroupApproximation.CharClass.LIXKGenOfPunctured
import GroupApproximation.CharClass.LIXKGenOfTopLine
import GroupApproximation.CharClass.ThomStepCLocalOf
import GroupApproximation.CharClass.LIXKCount
import GroupApproximation.CharClass.LIXLemmaTwoGenGlue
import GroupApproximation.Meta.AxiomGuard

/-!
# The Step C half of Lemma 2 at rank `n` with `k+1` zeros, over a field

Lane `lix-powers` (odd-`p` twins of lane `lix-oddside-n`'s rank-`n` Step C).

`CharClass/LIXKGenStepCHalf.lean` closes the Step C half at `F₂` from the open data
`KGen.KZeroStepCData`.  Over a field `K` the argument is the same count, with two differences:

* the count needs `((k+1 : ℕ) : K) ≠ 0`, i.e. `p ∤ k + 1` at `K = F_p`;
* the local classes do not agree for free.  Over `F₂` a nonzero class of a line is the
  generator; over `K` it is only a unit multiple of it (`isUnit_localEquivOf_of_ne_zero`), so
  `LocalClassesAgree` is a **field** of `KGen.KZeroStepCDataOf`, owned by lane `lix-oddside`
  (lead ruling 2026-09-12: the rotation carries zero `i` to zero `i+1` with orientation `+1`).

Every other input is a theorem here: the maps and their identities (`LIXKGenOfBundle`), the
local model (`LIXKGenOfModel`), punctured acyclicity (`LIXKGenOfPunctured`) and the top line
(`LIXKGenOfTopLine`).

## Main declarations

* `topChernClass_ne_zero_kzeroOf` — the abstract count over `K`, at the local model.
* `KGen.lixK_topClass_ne_zeroOf` — the rank-`n` instance.
* `KGen.KZeroStepCDataOf` — the open data over `K`.
* `KGen.stepCHalf_of_kZeroStepCDataOf` — **the Step C half over `K`, for `p ∤ k + 1`**.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

/-! ## 1. The abstract count over a field -/

/-- **Step C's odd side with `k` zeros over a field**, with `γ_r` pinned to the Thom class
through the section.  `i₀` is the zero at which the one-zero argument runs; the count needs the
local classes to agree and `k` to be a unit of `K`. -/
theorem topChernClass_ne_zero_kzeroOf {K : Type} [Field K] {N : Type} [TopologicalSpace N]
    {twoR : ℕ} {z₀ : N} (hacyclic : PuncturedAcyclicOf K N twoR z₀)
    {rel chart HrelE HE : ModuleCat.{0} K} {r k : ℕ} (i₀ : Fin k)
    {relLoc : Fin k → ModuleCat.{0} K}
    (j : rel ⟶ Hmod K (TopCat.of N) twoR)
    (rho : ∀ i, relLoc i ⟶ rel)
    (jloc : ∀ i, relLoc i ⟶ Hmod K (TopCat.of N) twoR)
    (hcompat : ∀ i, rho i ≫ j = jloc i)
    (ires : Hmod K (TopCat.of N) twoR ⟶ Hmod K (TopCat.of ↥({z₀}ᶜ : Set N)) twoR)
    (hexact : LinearMap.range (jloc i₀).hom = LinearMap.ker ires.hom)
    (absLine : Nonempty (Hmod K (TopCat.of N) twoR ≃ₗ[K] K))
    (exc : relLoc i₀ ≅ chart)
    (chartIso : chart ≅ relCohomology K (TopCat.of (Fin r → ℂ)) (puncturedSet r) (2 * r))
    (jE : HrelE ⟶ HE) (sRel : HrelE ⟶ rel)
    (sAbs : HE ⟶ Hmod K (TopCat.of N) twoR)
    (piStar : Hmod K (TopCat.of N) twoR ⟶ HE)
    (hnat : sRel ≫ j = jE ≫ sAbs)
    (hsection : piStar ≫ sAbs = 𝟙 (Hmod K (TopCat.of N) twoR))
    {u : HrelE} {xloc : ∀ i, relLoc i} (hsplit : LocalSplit rho (sRel.hom u) xloc)
    (hx : xloc i₀ ≠ 0)
    {c : Hmod K (TopCat.of N) twoR} (hloc : LocalClassesAgree jloc xloc c)
    (hk : ((k : ℕ) : K) ≠ 0)
    {gamma : Hmod K (TopCat.of N) twoR}
    (hu : jE.hom u = piStar.hom gamma) :
    gamma ≠ 0 := by
  have hgamma : j.hom (sRel.hom u) = gamma :=
    topClass_eq_of_naturality' jE j sRel sAbs piStar hnat hsection hu
  have hl : ∀ i, (jloc i).hom (xloc i) = c := hloc
  rw [← hgamma]
  exact map_ne_zero_of_localSplit j rho jloc hcompat hsplit hloc
    (topChernClass_ne_zero_of_chainOf hacyclic (jloc i₀) ires hexact absLine exc chartIso
      ⟨localEquivOf K r⟩ hx (hl i₀).symm)
    hk

namespace KGen

variable {ℓ : ℕ}

/-! ## 2. The rank-`n` instance -/

/-- **Step C's odd side with `k+1` zeros at rank `n`, over a field.** -/
theorem lixK_topClass_ne_zeroOf (K : Type) [Field K] (n k : ℕ) {dd : Fin ℓ → ℕ}
    (hdd : ∀ j, 0 < dd j) (i₀ : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    {u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd)}
    {xloc : ∀ i : Fin (k + 1), relCohomology K (lixN n dd)
      ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd)}
    (hsplit : LocalSplit (fun i => lixKRhoOf K n k dd i (2 * lixRank n dd))
      ((lixKSRelOf K n k hGc hGu hGe (2 * lixRank n dd)).hom u) xloc)
    (hx : xloc i₀ ≠ 0)
    {c : Hmod K (lixN n dd) (2 * lixRank n dd)}
    (hloc : LocalClassesAgree (fun i => lixKJlocOf K n k dd i (2 * lixRank n dd)) xloc c)
    (hk : ((k + 1 : ℕ) : K) ≠ 0)
    {gamma : Hmod K (lixN n dd) (2 * lixRank n dd)}
    (hclass : (lixJEOf K n hGc hGu (2 * lixRank n dd)).hom u
      = (lixPiStarOf K n hGc hGu (2 * lixRank n dd)).hom gamma) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_kzeroOf (puncturedAcyclic_lixKZeroOf K n k dd hdd i₀) i₀
    (lixKJOf K n k dd (2 * lixRank n dd))
    (fun i => lixKRhoOf K n k dd i (2 * lixRank n dd))
    (fun i => lixKJlocOf K n k dd i (2 * lixRank n dd))
    (fun i => lixK_hcompatOf K n k dd i (2 * lixRank n dd))
    (lixKIOf K n k dd i₀ (2 * lixRank n dd))
    (lixK_hexactOf K n k dd i₀ (2 * lixRank n dd))
    (absEquiv_lixNOf K n dd hdd)
    (lixKRelModelIsoOf K n k dd i₀ (2 * lixRank n dd)) (Iso.refl _)
    (lixJEOf K n hGc hGu (2 * lixRank n dd))
    (lixKSRelOf K n k hGc hGu hGe (2 * lixRank n dd))
    (lixKSAbsOf K n k hGc hGu hGe (2 * lixRank n dd))
    (lixPiStarOf K n hGc hGu (2 * lixRank n dd))
    (lixK_hnatOf K n k hGc hGu hGe (2 * lixRank n dd))
    (lixK_hsectionOf K n k hGc hGu hGe (2 * lixRank n dd))
    hsplit hx hloc hk hclass

/-! ## 3. The open data, and the Step C half -/

/-- **The open data of the `k`-zero Step C at rank `n` over a field `K`, for one corner unitary
`G` and one class `gamma`**: a relative class `u` of the bundle pair whose section pullback splits
into nonzero local classes with a common image `c`, and `u` restricting to `π^* gamma`. -/
def KZeroStepCDataOf (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    (gamma : Hmod K (lixN n dd) (2 * lixRank n dd)) : Prop :=
  ∃ (u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd))
    (xloc : ∀ i : Fin (k + 1), relCohomology K (lixN n dd)
      ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd))
    (c : Hmod K (lixN n dd) (2 * lixRank n dd)),
    LocalSplit (fun i => lixKRhoOf K n k dd i (2 * lixRank n dd))
        ((lixKSRelOf K n k hGc hGu hGe (2 * lixRank n dd)).hom u) xloc ∧
      (∀ i, xloc i ≠ 0) ∧
      LocalClassesAgree (fun i => lixKJlocOf K n k dd i (2 * lixRank n dd)) xloc c ∧
      (lixJEOf K n hGc hGu (2 * lixRank n dd)).hom u
        = (lixPiStarOf K n hGc hGu (2 * lixRank n dd)).hom gamma

/-- **The Step C half over a field, for the `k`-section with `p ∤ k + 1`.** -/
theorem stepCHalf_of_kZeroStepCDataOf (K : Type) [Field K] (n k : ℕ)
    (hk : ((k + 1 : ℕ) : K) ≠ 0) (dd : Fin ℓ → ℕ) (hdd : ∀ j, 0 < dd j)
    (topClass : (↥sphereOne × Gen.baseM n dd →
      Matrix (Gen.VIdx n dd ⊕ Gen.VIdx n dd) (Gen.VIdx n dd ⊕ Gen.VIdx n dd) ℂ) →
        Hmod K (lixN n dd) (2 * lixRank n dd))
    (hdata : ∀ (G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ)
      (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
      (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0),
      KZeroStepCDataOf K n k dd hGc hGu hGe
        (topClass (mappingTorus (Gen.Vmat n) G circHoriz circHeight))) :
    Gen.StepCHalf n dd (bVecK n k) topClass := by
  intro G hGc hGu hGe
  obtain ⟨_u, _xloc, _c, hsplit, hx, hloc, hclass⟩ := hdata G hGc hGu hGe
  exact lixK_topClass_ne_zeroOf K n k hdd 0 hGc hGu hGe hsplit (hx 0) hloc hk hclass

end KGen

/-! Audited on every build. -/

#audit_axioms topChernClass_ne_zero_kzeroOf
#audit_axioms KGen.lixK_topClass_ne_zeroOf
#audit_axioms KGen.stepCHalf_of_kZeroStepCDataOf

end GroupApproximation.CharClass
