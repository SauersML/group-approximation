import GroupApproximation.CharClass.LIXKGenLocalHomotopy
import GroupApproximation.CharClass.RelativeProdContractibleOf
import GroupApproximation.CharClass.RelativeLocalModelOf
import GroupApproximation.CharClass.ThomChartSquare
import GroupApproximation.Meta.AxiomGuard

/-!
# The fibre class at a zero is detected by restricting to the zero, over any field

Lane `lx-stepcK-local` (LIX strongest swarm, 2026-09-12).

`CharClass/LIXKGenOfLocalSquare.lean` reduces the local computation of Step C over a field to the
nonvanishing of the **fibre class** at each zero: the pullback of a class `u` of the bundle pair
along `lixKFibreMap`, the fibre over `z_i` in the standard frame.  A Thom class is computed by
restricting the bundle to a subset of the base, not along a map out of `ℂ^r`, so this file joins
the two.

Over the singleton `{z_i}` the fibre map is the slice at the point, followed by the inverse of the
trivialisation and the inclusion of the restricted total space.  The slice's pullback is an
isomorphism (a point is contractible, `relCohomologyProdIsoGenOf`), and so is the trivialisation's
(`relPairIso`), so a class that survives the restriction to the singleton survives the fibre map.

## Main declarations

* `KGen.lixKPtSet`, `KGen.lixKPt`, `KGen.lixKPtTriv` — the singleton at a zero and its trivialisation.
* `KGen.lixKFibreMap_eq_slice` — the fibre map is slice, trivialise back, include.
* `KGen.lixKFibre_relPullback_ne_zero_of_restrict` — **restriction to the zero detects the fibre
  class.**
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

/-! ## 1. The singleton at a zero -/

/-- The singleton at the `i`-th zero. -/
abbrev lixKPtSet (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) :
    Set (↥sphereOne × Gen.baseM n dd) :=
  {lixKZero n k dd i}

theorem lixKPtSet_subset_trivSet (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    lixKPtSet n k dd i ⊆ Bundle.trivSet (lixBundle n G hGc hGu) (lixKZero n k dd i) :=
  Set.singleton_subset_iff.mpr (Bundle.self_mem_trivSet _ _)

/-- The `i`-th zero, as a point of its singleton. -/
def lixKPt (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1)) : ↥(lixKPtSet n k dd i) :=
  ⟨lixKZero n k dd i, rfl⟩

/-- The trivialisation of the bundle over the singleton, in the standard frame at the zero. -/
def lixKPtTriv (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    Bundle.Total ((lixBundle n G hGc hGu).restrictTo (lixKPtSet n k dd i))
      ≃ₜ ↥(lixKPtSet n k dd i) × (Fin (lixRank n dd) → ℂ) :=
  Bundle.totalTrivStdOn (lixBundle n G hGc hGu) (lixKZero n k dd i) (lixKPtSet n k dd i)
    (lixKPtSet_subset_trivSet n k dd i hGc hGu) (lixRank n dd) (rank_lixBundle n G hGc hGu _)

/-- **The inverse trivialisation at the zero is the frame.** -/
theorem lixKPtTriv_symm_apply (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (y : Fin (lixRank n dd) → ℂ) :
    (lixKPtTriv n k dd i hGc hGu).symm (lixKPt n k dd i, y)
      = ⟨(lixKPt n k dd i, lixKGFrame n k i hGc hGu *ᵥ y), lixKFibre_mem n k dd i hGc hGu y⟩ := by
  refine (Homeomorph.symm_apply_eq _).mpr ?_
  refine Prod.ext rfl ?_
  show y = (lixKGFrame n k i hGc hGu)ᴴ *ᵥ
    (Bundle.intert (lixBundle n G hGc hGu) (lixKZero n k dd i) (lixKZero n k dd i)
      *ᵥ (lixKGFrame n k i hGc hGu *ᵥ y))
  rw [Bundle.intert_self, Matrix.one_mulVec, Matrix.mulVec_mulVec,
    lixKGFrame_conjTranspose_mul, Matrix.one_mulVec]

/-- The inverse trivialisation over the singleton, as an isomorphism of spaces.  Named with its
type so that `TopCat.isoOfHomeo` never has to infer its objects from a bare homeomorphism. -/
def lixKPtTrivIso (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    TopCat.of (↥(lixKPtSet n k dd i) × (Fin (lixRank n dd) → ℂ)) ≅
      TopCat.of (Bundle.Total ((lixBundle n G hGc hGu).restrictTo (lixKPtSet n k dd i))) :=
  TopCat.isoOfHomeo (lixKPtTriv n k dd i hGc hGu).symm

/-! ## 2. The fibre map, factored through the singleton -/

/-- **The fibre map is: slice at the zero, trivialise back, include.** -/
theorem lixKFibreMap_eq_slice (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    cmap (lixKFibreMap n k dd i hGc hGu)
      = RelativeSupport.sliceMap (lixKPt n k dd i) (Fin (lixRank n dd) → ℂ)
        ≫ ((lixKPtTrivIso n k dd i hGc hGu).hom
          ≫ cmap (Bundle.totalInclOn (lixBundle n G hGc hGu) (lixKPtSet n k dd i))) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  show lixKFibreMap n k dd i hGc hGu y
    = Bundle.totalInclOn (lixBundle n G hGc hGu) (lixKPtSet n k dd i)
        ((lixKPtTriv n k dd i hGc hGu).symm (lixKPt n k dd i, y))
  rw [lixKPtTriv_symm_apply n k dd i hGc hGu y]
  rfl

theorem lixKPtTriv_symm_mapsTo (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ∀ q ∈ {q : ↥(lixKPtSet n k dd i) × (Fin (lixRank n dd) → ℂ) | q.2 ≠ 0},
      (ConcreteCategory.hom (lixKPtTrivIso n k dd i hGc hGu).hom) q ∈
        ((Subtype.val : Bundle.Total ((lixBundle n G hGc hGu).restrictTo (lixKPtSet n k dd i))
            → ↥(lixKPtSet n k dd i) × (Gen.VIdx n dd ⊕ Gen.VIdx n dd → ℂ)) ⁻¹'
          Bundle.puncturedSet ((lixBundle n G hGc hGu).restrictTo (lixKPtSet n k dd i))) := by
  intro q hq
  refine ⟨((lixKPtTriv n k dd i hGc hGu).symm q).2, ?_⟩
  intro hzero
  refine hq ?_
  have h := (Bundle.totalTrivStdOn_snd_eq_zero_iff (lixBundle n G hGc hGu) (lixKZero n k dd i)
    (lixKPtSet n k dd i) (lixKPtSet_subset_trivSet n k dd i hGc hGu) (lixRank n dd)
    (rank_lixBundle n G hGc hGu _) ((lixKPtTriv n k dd i hGc hGu).symm q)).mpr hzero
  rwa [show (Bundle.totalTrivStdOn (lixBundle n G hGc hGu) (lixKZero n k dd i) (lixKPtSet n k dd i)
      (lixKPtSet_subset_trivSet n k dd i hGc hGu) (lixRank n dd) (rank_lixBundle n G hGc hGu _))
      ((lixKPtTriv n k dd i hGc hGu).symm q) = q from
    (lixKPtTriv n k dd i hGc hGu).apply_symm_apply q] at h

theorem lixKPtTriv_mapsTo (n k : ℕ) (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ∀ w ∈ ((Subtype.val : Bundle.Total ((lixBundle n G hGc hGu).restrictTo (lixKPtSet n k dd i))
            → ↥(lixKPtSet n k dd i) × (Gen.VIdx n dd ⊕ Gen.VIdx n dd → ℂ)) ⁻¹'
          Bundle.puncturedSet ((lixBundle n G hGc hGu).restrictTo (lixKPtSet n k dd i))),
      (ConcreteCategory.hom (lixKPtTrivIso n k dd i hGc hGu).inv) w ∈
        {q : ↥(lixKPtSet n k dd i) × (Fin (lixRank n dd) → ℂ) | q.2 ≠ 0} :=
  fun w hw h0 => hw.2 ((Bundle.totalTrivStdOn_snd_eq_zero_iff (lixBundle n G hGc hGu)
    (lixKZero n k dd i) (lixKPtSet n k dd i) (lixKPtSet_subset_trivSet n k dd i hGc hGu)
    (lixRank n dd) (rank_lixBundle n G hGc hGu _) w).mp h0)

/-! ## 3. Restriction to the zero detects the fibre class -/

/-- **A class that survives the restriction to the `i`-th zero has a nonzero fibre class there**,
over any field. -/
theorem lixKFibre_relPullback_ne_zero_of_restrict (K : Type) [Field K] (n k : ℕ)
    (dd : Fin ℓ → ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd))
    (hres : (relPullback K (cmap (Bundle.totalInclOn (lixBundle n G hGc hGu) (lixKPtSet n k dd i)))
      (totalInclOn_mapsTo (lixBundle n G hGc hGu) (lixKPtSet n k dd i))
        (2 * lixRank n dd)).hom u ≠ 0) :
    (relPullback K (cmap (lixKFibreMap n k dd i hGc hGu)) (lixKFibreMap_mapsTo n k dd i hGc hGu)
      (2 * lixRank n dd)).hom u ≠ 0 := by
  have hinc := totalInclOn_mapsTo (lixBundle n G hGc hGu) (lixKPtSet n k dd i)
  have htriv := lixKPtTriv_symm_mapsTo n k dd i hGc hGu
  have hslice := RelativeSupport.slice_mapsTo (lixKPt n k dd i) (puncturedSet (lixRank n dd))
  have h23 : ∀ q ∈ {q : ↥(lixKPtSet n k dd i) × (Fin (lixRank n dd) → ℂ) | q.2 ≠ 0},
      (ConcreteCategory.hom ((lixKPtTrivIso n k dd i hGc hGu).hom
        ≫ cmap (Bundle.totalInclOn (lixBundle n G hGc hGu) (lixKPtSet n k dd i)))) q
        ∈ lixPuncturedInTotal n hGc hGu :=
    fun q hq => hinc _ (htriv q hq)
  have h123 : ∀ y ∈ puncturedSet (lixRank n dd),
      (ConcreteCategory.hom (RelativeSupport.sliceMap (lixKPt n k dd i) (Fin (lixRank n dd) → ℂ)
        ≫ ((lixKPtTrivIso n k dd i hGc hGu).hom
          ≫ cmap (Bundle.totalInclOn (lixBundle n G hGc hGu) (lixKPtSet n k dd i))))) y
        ∈ lixPuncturedInTotal n hGc hGu :=
    fun y hy => h23 _ (hslice y hy)
  have e0 : relPullback K (cmap (lixKFibreMap n k dd i hGc hGu))
        (lixKFibreMap_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)
      = relPullback K (RelativeSupport.sliceMap (lixKPt n k dd i) (Fin (lixRank n dd) → ℂ)
          ≫ ((lixKPtTrivIso n k dd i hGc hGu).hom
            ≫ cmap (Bundle.totalInclOn (lixBundle n G hGc hGu) (lixKPtSet n k dd i)))) h123
          (2 * lixRank n dd) :=
    relPullback_eq_of_eq K (lixKFibreMap_eq_slice n k dd i hGc hGu)
      (lixKFibreMap_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)
  have e1 : relPullback K (RelativeSupport.sliceMap (lixKPt n k dd i) (Fin (lixRank n dd) → ℂ)
          ≫ ((lixKPtTrivIso n k dd i hGc hGu).hom
            ≫ cmap (Bundle.totalInclOn (lixBundle n G hGc hGu) (lixKPtSet n k dd i)))) h123
          (2 * lixRank n dd)
      = relPullback K ((lixKPtTrivIso n k dd i hGc hGu).hom
            ≫ cmap (Bundle.totalInclOn (lixBundle n G hGc hGu) (lixKPtSet n k dd i))) h23
          (2 * lixRank n dd)
        ≫ relPullback K (RelativeSupport.sliceMap (lixKPt n k dd i) (Fin (lixRank n dd) → ℂ))
          hslice (2 * lixRank n dd) :=
    relPullback_comp K _ _ hslice h23 h123 (2 * lixRank n dd)
  have e2 : relPullback K ((lixKPtTrivIso n k dd i hGc hGu).hom
            ≫ cmap (Bundle.totalInclOn (lixBundle n G hGc hGu) (lixKPtSet n k dd i))) h23
          (2 * lixRank n dd)
      = relPullback K (cmap (Bundle.totalInclOn (lixBundle n G hGc hGu) (lixKPtSet n k dd i)))
          hinc (2 * lixRank n dd)
        ≫ relPullback K (lixKPtTrivIso n k dd i hGc hGu).hom htriv
          (2 * lixRank n dd) :=
    relPullback_comp K _ _ htriv hinc h23 (2 * lixRank n dd)
  have h1 := ne_zero_of_isoOf
    (relPairIso K (lixKPtTrivIso n k dd i hGc hGu) htriv
      (lixKPtTriv_mapsTo n k dd i hGc hGu) (2 * lixRank n dd)) hres
  have h2 := ne_zero_of_isoOf
    (RelativeSupport.relCohomologyProdIsoGenOf K inferInstance (lixKPt n k dd i)
      (2 * lixRank n dd) (two_le_two_mul_lixRank n dd) (puncturedSet (lixRank n dd))) h1
  rw [e0, e1, e2]
  exact h2

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.lixKFibreMap_eq_slice
#audit_axioms KGen.lixKFibre_relPullback_ne_zero_of_restrict

end GroupApproximation.CharClass
