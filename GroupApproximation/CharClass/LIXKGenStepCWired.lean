import GroupApproximation.CharClass.LIXKGenBundle
import GroupApproximation.CharClass.LIXKStepCTwo
import GroupApproximation.CharClass.ThomEulerNaturality
import GroupApproximation.Meta.AxiomGuard

/-!
# Step C's odd side with `k+1` zeros at rank `n`, wired to the rank-`n` LIX objects

Lane `lix-oddside-n` (predecessor report `sp-oddside-n.md` §0.3, file F; lead rulings of
2026-09-11 21:35 and 21:55).

This is `CharClass/LIXKStepCWired.lean` with the rank a parameter and the constant section at
`e₀`, over the vocabulary of `CharClass/LIXKGenBundle.lean`.  The counting engine
(`LIXKCount`, `LIXKStepC`, `LIXKStepCTwo`) is rank-free and is cited verbatim.

## What is discharged here, and what is left open

Discharged, at every rank:

* the punctured acyclicity at every one of the `k+1` zeros (`puncturedAcyclic_lixKZero`), from
  `KGen.puncturedAcyclic_lixBase_topDegree`, so the rank-two binder `hacyclic` is gone;
* the `k+1` restriction maps, their compatibility, exactness at each zero, naturality along the
  section and the splitting `s ≫ π = 𝟙` (`LIXKGenBundle`).

Left open, each a binder with a named route:

* `hsplit : LocalSplit …` — relative Mayer–Vietoris over the `k+1` punctures (`LIXKRelativeMV`,
  rank-free at the cochain level);
* `hx`, `exc`, `chartIso` — the one-zero local computation at each zero: the chart half is
  `KGen.lixLocalRelIso` (`CharClass/LIXKGenLocalHomeo.lean`), and by
  `KGen.kSect_joinC_of_mem_kSector` the section read in the chart at the `i`-th zero is the same
  trivial block at every `i`;
* `absLine` — `H^{2r}(N; F₂)` is a line;
* `hclass` — the Thom class pulls back to `gamma`.

At `p = 2` the local classes agree for free (`LIXKStepCTwo`), so `lixK_topClass_ne_zero_two`
has no `LocalClassesAgree` binder.

## Main declarations

* `KGen.puncturedAcyclic_lixKZero`.
* `KGen.lixK_topClass_ne_zero` — the naturality form, over `LocalClassesAgree`.
* `KGen.lixK_topClass_ne_zero_two` — the mod-2 form, local data at every zero.
* `KGen.lixK_topClass_ne_zero_two_odd` — the exponent-facing form for an odd number of zeros.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open scoped Matrix
open CategoryTheory Limits
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. Punctured acyclicity at the zeros -/

/-- **The rank-`n` LIX base is top-punctured acyclic at each of the `k+1` zeros.** -/
theorem puncturedAcyclic_lixKZero (n k : ℕ) (dd : Fin ℓ → ℕ) (hdd : ∀ j, 0 < dd j)
    (i : Fin (k + 1)) :
    PuncturedAcyclic (↥sphereOne × Gen.baseM n dd) (2 * lixRank n dd) (lixKZero n k dd i) := by
  have h := puncturedAcyclic_lixBase_topDegree n dd hdd (lixKZero n k dd i)
  rwa [lixTopDegree_eq_two_mul_lixRank] at h

/-! ## 2. The naturality form -/

/-- **Step C's odd side with `k+1` zeros at rank `n`**, over `LocalClassesAgree`. -/
theorem lixK_topClass_ne_zero (n k : ℕ) (i₀ : Fin (k + 1)) (hdd : ∀ j, 0 < dd j)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    (absLine : Nonempty
      (cohomologyZMod2 (lixN n dd) (2 * lixRank n dd) ≃ₗ[ZMod 2] ZMod 2))
    {chart : ModuleCat.{0} (ZMod 2)}
    (exc : relCohomology (ZMod 2) (lixN n dd)
      ({lixKZero n k dd i₀}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd) ≅ chart)
    (chartIso : chart ≅ relCohomology (ZMod 2) (TopCat.of (Fin (lixRank n dd) → ℂ))
      (puncturedSet (lixRank n dd)) (2 * lixRank n dd))
    {u : relCohomology (ZMod 2) (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd)}
    {xloc : ∀ i : Fin (k + 1), relCohomology (ZMod 2) (lixN n dd)
      ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd)}
    (hsplit : LocalSplit (fun i => lixKRho n k dd i (2 * lixRank n dd))
      ((lixKSRel n k hGc hGu hGe (2 * lixRank n dd)).hom u) xloc)
    (hx : xloc i₀ ≠ 0)
    {c : cohomologyZMod2 (lixN n dd) (2 * lixRank n dd)}
    (hloc : LocalClassesAgree (fun i => lixKJloc n k dd i (2 * lixRank n dd)) xloc c)
    (hk : ((k + 1 : ℕ) : ZMod 2) ≠ 0)
    {gamma : cohomologyZMod2 (lixN n dd) (2 * lixRank n dd)}
    (hclass : (lixJE n hGc hGu (2 * lixRank n dd)).hom u
      = (lixPiStar n hGc hGu (2 * lixRank n dd)).hom gamma) :
    gamma ≠ 0 :=
  topChernClass_ne_zero_kzero_naturality (puncturedAcyclic_lixKZero n k dd hdd i₀) i₀
    (lixKJ n k dd (2 * lixRank n dd))
    (fun i => lixKRho n k dd i (2 * lixRank n dd))
    (fun i => lixKJloc n k dd i (2 * lixRank n dd))
    (fun i => lixK_hcompat n k dd i (2 * lixRank n dd))
    (lixKI n k dd i₀ (2 * lixRank n dd))
    (lixK_hexact n k dd i₀ (2 * lixRank n dd))
    absLine exc chartIso
    (lixJE n hGc hGu (2 * lixRank n dd))
    (lixKSRel n k hGc hGu hGe (2 * lixRank n dd))
    (lixKSAbs n k hGc hGu hGe (2 * lixRank n dd))
    (lixPiStar n hGc hGu (2 * lixRank n dd))
    (lixK_hnat n k hGc hGu hGe (2 * lixRank n dd))
    (lixK_hsection n k hGc hGu hGe (2 * lixRank n dd))
    hsplit hx hloc hk hclass

/-! ## 3. The mod-2 form, with local data at every zero -/

/-- **Step C's odd side with `k+1` zeros at rank `n`, mod 2.**  `LocalClassesAgree` is gone:
every zero carries the one-zero data, and an `F₂`-line has one nonzero element. -/
theorem lixK_topClass_ne_zero_two (n k : ℕ) (hdd : ∀ j, 0 < dd j)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    (absLine : Nonempty
      (cohomologyZMod2 (lixN n dd) (2 * lixRank n dd) ≃ₗ[ZMod 2] ZMod 2))
    {chart : Fin (k + 1) → ModuleCat.{0} (ZMod 2)}
    (exc : ∀ i, relCohomology (ZMod 2) (lixN n dd)
      ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd) ≅ chart i)
    (chartIso : ∀ i, chart i ≅ relCohomology (ZMod 2) (TopCat.of (Fin (lixRank n dd) → ℂ))
      (puncturedSet (lixRank n dd)) (2 * lixRank n dd))
    {u : relCohomology (ZMod 2) (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd)}
    {xloc : ∀ i : Fin (k + 1), relCohomology (ZMod 2) (lixN n dd)
      ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd)}
    (hsplit : LocalSplit (fun i => lixKRho n k dd i (2 * lixRank n dd))
      ((lixKSRel n k hGc hGu hGe (2 * lixRank n dd)).hom u) xloc)
    (hx : ∀ i, xloc i ≠ 0)
    (hk : ((k + 1 : ℕ) : ZMod 2) ≠ 0)
    {gamma : cohomologyZMod2 (lixN n dd) (2 * lixRank n dd)}
    (hclass : (lixJE n hGc hGu (2 * lixRank n dd)).hom u
      = (lixPiStar n hGc hGu (2 * lixRank n dd)).hom gamma) :
    gamma ≠ 0 := by
  have hgamma : (lixKJ n k dd (2 * lixRank n dd)).hom
      ((lixKSRel n k hGc hGu hGe (2 * lixRank n dd)).hom u) = gamma :=
    topClass_eq_of_naturality' (lixJE n hGc hGu (2 * lixRank n dd))
      (lixKJ n k dd (2 * lixRank n dd))
      (lixKSRel n k hGc hGu hGe (2 * lixRank n dd))
      (lixKSAbs n k hGc hGu hGe (2 * lixRank n dd))
      (lixPiStar n hGc hGu (2 * lixRank n dd))
      (lixK_hnat n k hGc hGu hGe (2 * lixRank n dd))
      (lixK_hsection n k hGc hGu hGe (2 * lixRank n dd)) hclass
  rw [← hgamma]
  exact topChernClass_ne_zero_kzero_two (k := k + 1) 0 (lixKZero n k dd)
    (puncturedAcyclic_lixKZero n k dd hdd)
    (lixKJ n k dd (2 * lixRank n dd))
    (fun i => lixKRho n k dd i (2 * lixRank n dd))
    (fun i => lixKJloc n k dd i (2 * lixRank n dd))
    (fun i => lixK_hcompat n k dd i (2 * lixRank n dd))
    (fun i => lixKI n k dd i (2 * lixRank n dd))
    (fun i => lixK_hexact n k dd i (2 * lixRank n dd))
    absLine exc chartIso hsplit hx hk

/-- **The exponent-facing form**: for an odd number `k + 1` of zeros, the `k`-section's top
class is nonzero.  With the lead's family ruling (exponent `e` ↔ `bVecK n (e − 1)`), this is
the Step C half at `p = 2` for every odd exponent `e = k + 1`. -/
theorem lixK_topClass_ne_zero_two_odd (n k : ℕ) (hodd : Odd (k + 1)) (hdd : ∀ j, 0 < dd j)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    (absLine : Nonempty
      (cohomologyZMod2 (lixN n dd) (2 * lixRank n dd) ≃ₗ[ZMod 2] ZMod 2))
    {chart : Fin (k + 1) → ModuleCat.{0} (ZMod 2)}
    (exc : ∀ i, relCohomology (ZMod 2) (lixN n dd)
      ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd) ≅ chart i)
    (chartIso : ∀ i, chart i ≅ relCohomology (ZMod 2) (TopCat.of (Fin (lixRank n dd) → ℂ))
      (puncturedSet (lixRank n dd)) (2 * lixRank n dd))
    {u : relCohomology (ZMod 2) (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd)}
    {xloc : ∀ i : Fin (k + 1), relCohomology (ZMod 2) (lixN n dd)
      ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd)}
    (hsplit : LocalSplit (fun i => lixKRho n k dd i (2 * lixRank n dd))
      ((lixKSRel n k hGc hGu hGe (2 * lixRank n dd)).hom u) xloc)
    (hx : ∀ i, xloc i ≠ 0)
    {gamma : cohomologyZMod2 (lixN n dd) (2 * lixRank n dd)}
    (hclass : (lixJE n hGc hGu (2 * lixRank n dd)).hom u
      = (lixPiStar n hGc hGu (2 * lixRank n dd)).hom gamma) :
    gamma ≠ 0 :=
  lixK_topClass_ne_zero_two n k hdd hGc hGu hGe absLine exc chartIso hsplit hx
    (natCast_ne_zero_zmod_two hodd) hclass

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.puncturedAcyclic_lixKZero
#audit_axioms KGen.lixK_topClass_ne_zero
#audit_axioms KGen.lixK_topClass_ne_zero_two
#audit_axioms KGen.lixK_topClass_ne_zero_two_odd

end GroupApproximation.CharClass
