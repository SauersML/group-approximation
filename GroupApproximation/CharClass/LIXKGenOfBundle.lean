import GroupApproximation.CharClass.LIXKGenBundle
import GroupApproximation.CharClass.RelativeProdContractibleOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The maps of the `k`-zero Step C at rank `n`, over a field

Lane `lix-powers` (odd-`p` twins of lane `lix-oddside-n`'s rank-`n` Step C).

`CharClass/LIXKGenBundle.lean` builds the bundle pair, the `k`-fold section and the `k+1`
restriction maps at `F₂`.  The spaces, the section and the maps of pairs carry no coefficients;
only the cohomology functors do, and those are stated over any commutative ring
(`relToAbs`, `relPullback`, `absToSub`, `absPullOf`).  This file re-instantiates the maps over a
field `K` and re-proves the four identities the Step C engine consumes.

## Main declarations

* `KGen.lixJEOf`, `lixKSRelOf`, `lixKSAbsOf`, `lixPiStarOf` — the bundle pair.
* `KGen.lixKJOf`, `lixKJlocOf`, `lixKIOf`, `lixKRhoOf` — the base pair and the restrictions.
* `KGen.lixK_hexactOf`, `lixK_hcompatOf`, `lixK_hnatOf`, `lixK_hsectionOf`.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The bundle pair -/

/-- `jE` over `K`: the relative-to-absolute map of the bundle pair. -/
def lixJEOf (K : Type) [Field K] (n : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) (q : ℕ) :
    relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu) q ⟶
      Hmod K (lixTotalPair n hGc hGu) q :=
  relToAbs K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu) q

/-- `sRel` over `K` at the `k+1`-punctured base. -/
def lixKSRelOf (K : Type) [Field K] (n k : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) (q : ℕ) :
    relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu) q ⟶
      relCohomology K (lixN n dd)
        ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q :=
  relPullback K (lixKS n k hGc hGu hGe) (lixKSectionTotal_mapsTo n k hGc hGu hGe) q

/-- `sAbs` over `K` for the `k`-fold section. -/
def lixKSAbsOf (K : Type) [Field K] (n k : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) (q : ℕ) :
    Hmod K (lixTotalPair n hGc hGu) q ⟶ Hmod K (lixN n dd) q :=
  absPullOf K (lixKS n k hGc hGu hGe) q

/-- `piStar` over `K`: the absolute pullback along the bundle projection. -/
def lixPiStarOf (K : Type) [Field K] (n : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) (q : ℕ) :
    Hmod K (lixN n dd) q ⟶ Hmod K (lixTotalPair n hGc hGu) q :=
  absPullOf K (lixPi n hGc hGu) q

/-! ## 2. The base pair with `k+1` punctures, and the `k+1` restrictions -/

/-- `j` over `K` for the `k+1`-punctured pair. -/
def lixKJOf (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ) (q : ℕ) :
    relCohomology K (lixN n dd)
        ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q ⟶
      Hmod K (lixN n dd) q :=
  relToAbs K (lixN n dd) ((lixKZeroSet n k dd)ᶜ) q

/-- `j_i` over `K` for the single-puncture pair at the `i`-th zero. -/
def lixKJlocOf (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) (q : ℕ) :
    relCohomology K (lixN n dd)
        ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q ⟶
      Hmod K (lixN n dd) q :=
  relToAbs K (lixN n dd) ({lixKZero n k dd i}ᶜ) q

/-- `i` over `K`: restriction to the complement of the `i`-th zero. -/
def lixKIOf (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) (q : ℕ) :
    Hmod K (lixN n dd) q ⟶
      Hmod K (TopCat.of ↥({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd))) q :=
  absToSub (X := lixN n dd) K ({lixKZero n k dd i}ᶜ) q

/-- Exactness of the pair sequence at the absolute group, at the `i`-th zero, over `K`. -/
theorem lixK_hexactOf (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (q : ℕ) :
    LinearMap.range (lixKJlocOf K n k dd i q).hom = LinearMap.ker (lixKIOf K n k dd i q).hom :=
  relLES_range_eq_ker' K (lixN n dd) ({lixKZero n k dd i}ᶜ) q

/-- `ρ_i` over `K`, the relative pullback along the identity of `N`. -/
def lixKRhoOf (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) (q : ℕ) :
    relCohomology K (lixN n dd)
        ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q ⟶
      relCohomology K (lixN n dd)
        ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q :=
  relPullback K (𝟙 (lixN n dd)) (lixK_mapsTo n k dd i) q

/-- **`ρ_i ≫ j = j_i`** over `K`, by naturality of `relToAbs` along the identity. -/
theorem lixK_hcompatOf (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    (q : ℕ) :
    lixKRhoOf K n k dd i q ≫ lixKJOf K n k dd q = lixKJlocOf K n k dd i q := by
  have h : lixKJlocOf K n k dd i q ≫ absPullOf K (𝟙 (lixN n dd)) q
      = lixKRhoOf K n k dd i q ≫ lixKJOf K n k dd q :=
    relToAbs_naturality K (𝟙 (lixN n dd)) (lixK_mapsTo n k dd i) q
  rw [absPull_id_eqOf, Category.comp_id] at h
  exact h.symm

/-! ## 3. Naturality and the splitting -/

/-- `hnat` over `K` for the `k`-fold section at rank `n`. -/
theorem lixK_hnatOf (K : Type) [Field K] (n k : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) (q : ℕ) :
    lixKSRelOf K n k hGc hGu hGe q ≫ lixKJOf K n k dd q
      = lixJEOf K n hGc hGu q ≫ lixKSAbsOf K n k hGc hGu hGe q :=
  (relToAbs_naturality K (lixKS n k hGc hGu hGe) (lixKSectionTotal_mapsTo n k hGc hGu hGe) q).symm

/-- `hsection` over `K` for the `k`-fold section at rank `n`. -/
theorem lixK_hsectionOf (K : Type) [Field K] (n k : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) (q : ℕ) :
    lixPiStarOf K n hGc hGu q ≫ lixKSAbsOf K n k hGc hGu hGe q = 𝟙 (Hmod K (lixN n dd) q) := by
  rw [lixPiStarOf, lixKSAbsOf, ← absPull_compOf, lixKS_comp_lixPi, absPull_id_eqOf]

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.lixK_hexactOf
#audit_axioms KGen.lixK_hcompatOf
#audit_axioms KGen.lixK_hnatOf
#audit_axioms KGen.lixK_hsectionOf

end GroupApproximation.CharClass
