import GroupApproximation.CharClass.LIXKGenSection
import GroupApproximation.CharClass.LIXKGenPunctured
import GroupApproximation.CharClass.LIXShapeGenericRank
import GroupApproximation.CharClass.LIXStepCOddRelative
import GroupApproximation.Meta.AxiomGuard

/-!
# The mapping torus at rank `n` as a bundle, its punctured pair, and the `k`-section into it

Lane `lix-oddside-n` (lead ruling 2026-09-11 21:50: the rank-`n` bundle vocabulary is this lane's,
built additively under `CharClass/LIXKGenBundle*`; `RelativeSupport*` and the rank-two files are
not edited).

The rank-two vocabulary is spread over `LemmaTwoTopClass` (`lixN`), `LIXBundleModel`
(`lixBundle`, `rank_lixBundle`), `LIXBundlePair` (`lixTotalPair`, `lixPuncturedInTotal`, the
section into the total space, `lixSRel`), `LIXStepCOddRelative` (`lixS`, `lixPi`, `lixHE`,
`lixJE`, `lixSAbs`, `lixPiStar`, `lixHnat`, `lixHsection`) and `LIXKStepCWired` (the `k+1`
restrictions and their compatibility).  Every one of them is over `baseM dd`, i.e. at rank two.
This file states them over `Gen.baseM n dd` for the `k`-section `KGen.lixKSection n k G` of
`CharClass/LIXKGenSection.lean`, whose constant section is at `e₀`.  Nothing here is new
mathematics: each proof is the rank-two one with the rank a parameter.

## Main declarations

* `KGen.lixN`, `KGen.lixBundle`, `KGen.rank_lixBundle`.
* `KGen.lixTotalPair`, `KGen.lixPuncturedInTotal`.
* `KGen.lixKSectionTotal`, `lixKSectionTotal_mapsTo`, `lixKSRel`, `lixKS`, `lixPi`,
  `lixKS_comp_lixPi`.
* `KGen.lixHE`, `lixJE`, `lixKSAbs`, `lixPiStar`, `lixK_hnat`, `lixK_hsection`.
* `KGen.lixKJ`, `lixKJloc`, `lixKI`, `lixK_hexact`, `lixKRho`, `lixK_hcompat`.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The base and the bundle -/

/-- The base `N = S¹ × S^{2n+1} × ∏ⱼ ℂP^{dⱼ}` at rank `n`, as an object of `TopCat`. -/
def lixN (n : ℕ) (dd : Fin ℓ → ℕ) : TopCat.{0} := TopCat.of (↥sphereOne × Gen.baseM n dd)

theorem continuous_mappingTorus_lix (n : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ} (hGc : Continuous G) :
    Continuous (mappingTorus (Gen.Vmat n) G circHoriz circHeight) :=
  mappingTorus_continuous (Gen.continuous_Vmat n) hGc isCircleChart_sphereOne

theorem isStarProjection_mappingTorus_lix (n : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) (p : ↥sphereOne × Gen.baseM n dd) :
    IsStarProjection (mappingTorus (Gen.Vmat n) G circHoriz circHeight p) :=
  mappingTorus_isStarProjection hGu isCircleChart_sphereOne p

/-- **The mapping torus `W_g` at rank `n`, as a bundle over `S¹ × S^{2n+1} × ∏ⱼ ℂP^{dⱼ}`.** -/
def lixBundle (n : ℕ) (G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ)
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    Bundle (↥sphereOne × Gen.baseM n dd) (Gen.VIdx n dd ⊕ Gen.VIdx n dd) where
  toFun := mappingTorus (Gen.Vmat n) G circHoriz circHeight
  continuous_toFun := continuous_mappingTorus_lix n hGc
  isStarProjection_toFun := isStarProjection_mappingTorus_lix n hGu

@[simp] theorem coe_lixBundle (n : ℕ)
    (G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ)
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ⇑(lixBundle n G hGc hGu) = mappingTorus (Gen.Vmat n) G circHoriz circHeight := rfl

/-- **`rank W_g = rank V = (∑ⱼ dⱼ) + (n+1)`, everywhere.** -/
theorem rank_lixBundle (n : ℕ) (G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ)
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (p : ↥sphereOne × Gen.baseM n dd) :
    (lixBundle n G hGc hGu).rank p = lixRank n dd := by
  have htr : Matrix.trace ((lixBundle n G hGc hGu) p) = ((lixRank n dd : ℕ) : ℂ) := by
    show Matrix.trace (mappingTorus (Gen.Vmat n) G circHoriz circHeight p) = _
    rw [trace_mappingTorus]
    exact Gen.trace_Vmat n p.2
  have h := Bundle.trace_eq_rank (lixBundle n G hGc hGu) p
  rw [htr] at h
  exact_mod_cast h.symm

/-! ## 2. The bundle pair -/

/-- The total space of the mapping torus at rank `n`, as a `TopCat` object. -/
def lixTotalPair (n : ℕ) {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) : TopCat.{0} :=
  TopCat.of (Bundle.Total (lixBundle n G hGc hGu))

/-- The complement of the zero section, as a subset of the total space. -/
def lixPuncturedInTotal (n : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    Set (Bundle.Total (lixBundle n G hGc hGu)) :=
  (Subtype.val : Bundle.Total (lixBundle n G hGc hGu) → _) ⁻¹'
    Bundle.puncturedSet (lixBundle n G hGc hGu)

/-! ## 3. The `k`-section into the total space -/

/-- The `k`-fold section at rank `n`, into the total space of the bundle. -/
def lixKSectionTotal (n k : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) :
    C(↥sphereOne × Gen.baseM n dd, Bundle.Total (lixBundle n G hGc hGu)) where
  toFun x := ⟨(x, lixKSection n k G x), lixKSection_mem n k hGu x⟩
  continuous_toFun :=
    (continuous_id.prodMk (lixKSection_continuous n hGc hGu hGe)).subtype_mk _

/-- **The section carries the `k+1`-punctured base into the punctured total space.** -/
theorem lixKSectionTotal_mapsTo (n k : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) :
    ∀ x ∈ ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)),
      (ConcreteCategory.hom (cmap (lixKSectionTotal n k hGc hGu hGe))) x ∈
        lixPuncturedInTotal n hGc hGu := by
  intro x hx
  refine ⟨lixKSection_mem n k hGu x, ?_⟩
  intro hzero
  exact lixKSection_ne_zero_of_notMem n hGe hx hzero

/-- `sRel` at the `k+1`-punctured base, at rank `n`. -/
def lixKSRel (n k : ℕ) {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) (q : ℕ) :
    relCohomology (ZMod 2) (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu) q ⟶
      relCohomology (ZMod 2) (lixN n dd)
        ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q :=
  relPullback (ZMod 2) (cmap (lixKSectionTotal n k hGc hGu hGe))
    (lixKSectionTotal_mapsTo n k hGc hGu hGe) q

/-- The section, as a morphism of spaces. -/
def lixKS (n k : ℕ) {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) :
    lixN n dd ⟶ lixTotalPair n hGc hGu :=
  cmap (lixKSectionTotal n k hGc hGu hGe)

/-- The bundle projection, as a morphism of spaces. -/
def lixPi (n : ℕ) {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    lixTotalPair n hGc hGu ⟶ lixN n dd :=
  cmap (Bundle.totalPi (lixBundle n G hGc hGu))

theorem lixKS_comp_lixPi (n k : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) :
    lixKS n k hGc hGu hGe ≫ lixPi n hGc hGu = 𝟙 (lixN n dd) := rfl

/-! ## 4. The absolute and relative groups of the bundle pair -/

/-- `HE`: the absolute cohomology of the total space. -/
abbrev lixHE (n : ℕ) {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) (q : ℕ) :
    ModuleCat.{0} (ZMod 2) :=
  cohomologyZMod2 (lixTotalPair n hGc hGu) q

/-- `jE`: the relative-to-absolute map of the bundle pair. -/
def lixJE (n : ℕ) {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) (q : ℕ) :
    relCohomology (ZMod 2) (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu) q ⟶
      lixHE n hGc hGu q :=
  relToAbs (ZMod 2) (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu) q

/-- `sAbs` for the `k`-fold section. -/
def lixKSAbs (n k : ℕ) {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) (q : ℕ) :
    lixHE n hGc hGu q ⟶ cohomologyZMod2 (lixN n dd) q :=
  RelativeSupport.absPull (lixKS n k hGc hGu hGe) q

/-- `piStar`: the absolute pullback along the bundle projection. -/
def lixPiStar (n : ℕ) {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) (q : ℕ) :
    cohomologyZMod2 (lixN n dd) q ⟶ lixHE n hGc hGu q :=
  RelativeSupport.absPull (lixPi n hGc hGu) q

/-! ## 5. The base pair with `k+1` punctures, and the `k+1` restrictions -/

/-- `j` for the `k+1`-punctured pair. -/
def lixKJ (n k : ℕ) (dd : Fin ℓ → ℕ) (q : ℕ) :
    relCohomology (ZMod 2) (lixN n dd)
        ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q ⟶
      cohomologyZMod2 (lixN n dd) q :=
  relToAbs (ZMod 2) (lixN n dd) ((lixKZeroSet n k dd)ᶜ) q

/-- `j_i` for the single-puncture pair at the `i`-th zero. -/
def lixKJloc (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) (q : ℕ) :
    relCohomology (ZMod 2) (lixN n dd)
        ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q ⟶
      cohomologyZMod2 (lixN n dd) q :=
  relToAbs (ZMod 2) (lixN n dd) ({lixKZero n k dd i}ᶜ) q

/-- `i`: restriction to the complement of the `i`-th zero. -/
def lixKI (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) (q : ℕ) :
    cohomologyZMod2 (lixN n dd) q ⟶
      cohomologyZMod2
        (TopCat.of ↥({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd))) q :=
  absToSub (X := lixN n dd) (ZMod 2) ({lixKZero n k dd i}ᶜ) q

/-- Exactness of the pair sequence at the absolute group, at the `i`-th zero. -/
theorem lixK_hexact (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) (q : ℕ) :
    LinearMap.range (lixKJloc n k dd i q).hom = LinearMap.ker (lixKI n k dd i q).hom :=
  relLES_range_eq_ker (lixN n dd) ({lixKZero n k dd i}ᶜ) q

/-- The identity of `N` is a map of pairs from the `k+1`-punctured pair to the pair
punctured at the `i`-th zero only. -/
theorem lixK_mapsTo (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    ∀ x ∈ ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)),
      (ConcreteCategory.hom (𝟙 (lixN n dd))) x ∈
        ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) := by
  intro x hx
  show x ∉ ({lixKZero n k dd i} : Set (↥sphereOne × Gen.baseM n dd))
  intro hmem
  exact hx ((mem_lixKZeroSet_iff n k dd x).mpr ⟨i, hmem⟩)

/-- `ρ_i`, the relative pullback along that map of pairs. -/
def lixKRho (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) (q : ℕ) :
    relCohomology (ZMod 2) (lixN n dd)
        ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q ⟶
      relCohomology (ZMod 2) (lixN n dd)
        ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q :=
  relPullback (ZMod 2) (𝟙 (lixN n dd)) (lixK_mapsTo n k dd i) q

/-- **`ρ_i ≫ j = j_i`**, by naturality of `relToAbs` along the identity. -/
theorem lixK_hcompat (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) (q : ℕ) :
    lixKRho n k dd i q ≫ lixKJ n k dd q = lixKJloc n k dd i q := by
  have h : lixKJloc n k dd i q ≫ RelativeSupport.absPull (𝟙 (lixN n dd)) q
      = lixKRho n k dd i q ≫ lixKJ n k dd q :=
    relToAbs_naturality (ZMod 2) (𝟙 (lixN n dd)) (lixK_mapsTo n k dd i) q
  rw [RelativeSupport.absPull_id_eq, Category.comp_id] at h
  exact h.symm

/-! ## 6. Naturality and the splitting -/

/-- `hnat` for the `k`-fold section at rank `n`. -/
theorem lixK_hnat (n k : ℕ) {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) (q : ℕ) :
    lixKSRel n k hGc hGu hGe q ≫ lixKJ n k dd q
      = lixJE n hGc hGu q ≫ lixKSAbs n k hGc hGu hGe q :=
  (relToAbs_naturality (ZMod 2) (lixKS n k hGc hGu hGe)
    (lixKSectionTotal_mapsTo n k hGc hGu hGe) q).symm

/-- `hsection` for the `k`-fold section at rank `n`. -/
theorem lixK_hsection (n k : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) (q : ℕ) :
    lixPiStar n hGc hGu q ≫ lixKSAbs n k hGc hGu hGe q = 𝟙 (cohomologyZMod2 (lixN n dd) q) := by
  rw [lixPiStar, lixKSAbs, ← RelativeSupport.absPull_comp, lixKS_comp_lixPi,
    RelativeSupport.absPull_id_eq]

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.rank_lixBundle
#audit_axioms KGen.lixKSectionTotal_mapsTo
#audit_axioms KGen.lixK_hcompat
#audit_axioms KGen.lixK_hnat
#audit_axioms KGen.lixK_hsection

end GroupApproximation.CharClass
