import GroupApproximation.CharClass.LIXKGenLocalSplit
import GroupApproximation.CharClass.LIXKGenOfBundle
import GroupApproximation.CharClass.RelativeSplitField
import GroupApproximation.Meta.AxiomGuard

/-!
# The split and the nonvanishing of the local classes over a field, at rank `n`

Lane `lix-oddside` (lead ruling 2026-09-11: the `K` versions of leaves (3) and (4) of the
`k`-zero Step C data, additively beside the `F₂` ones in `CharClass/LIXKGenLocalSplit.lean`).

The finite-puncture induction `LIXKRelMV.exists_localSplit_of_acyclic` takes the acyclicity of
the small-annihilator complex as input; over a field it is lix-coeff's
`exists_smallAnnOf_preimage`.  The restriction argument `xloc_ne_zero_of_restrictTo_ne_zero`
is already stated over any commutative ring.

## Main declarations

* `LIXKRelMV.exists_localSplitOf` — the finite-puncture split over a field, for any T₁ space.
* `KGen.exists_localSplit_kgenOf` — (4) over `K` at rank `n`, in lix-powers' `lixKRhoOf` shape.
* `KGen.KGenLocalNonzeroOf`, `KGen.exists_localSplit_ne_zero_kgenOf` — (4) and (3) over `K`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

namespace LIXKRelMV

/-- **The finite-puncture split over a field.** -/
theorem exists_localSplitOf (K : Type) [Field K] {X : TopCat.{0}} [T1Space X] {k : ℕ}
    (z : Fin k → X) (hz : Function.Injective z) {C : Set X} (hC : ∀ y, y ∈ C ↔ ∀ i, y ≠ z i)
    (n : ℕ) (x : relCohomology K X C n) :
    ∃ xloc : ∀ i, relCohomology K X ({z i}ᶜ : Set X) n,
      LocalSplit (fun i => relPullback K (𝟙 X) (mapsTo_compl_puncture hC i) n) x xloc :=
  exists_localSplit_of_acyclic n
    (fun U V hUV w hw => exists_smallAnnOf_preimage K X (twoSetCover U V hUV) n w hw)
    k z hz C hC x

end LIXKRelMV

namespace KGen

variable {ℓ : ℕ}

/-- **(4) over `K`: the local split, for every class of the `k + 1`-punctured pair.** -/
theorem exists_localSplit_kgenOf (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ) (q : ℕ)
    (x : relCohomology K (lixN n dd)
      ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q) :
    ∃ xloc : ∀ i : Fin (k + 1), relCohomology K (lixN n dd)
        ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q,
      LocalSplit (fun i => lixKRhoOf K n k dd i q) x xloc :=
  LIXKRelMV.exists_localSplitOf K (X := lixN n dd) (lixKZero n k dd)
    (lixKZero_injective n k dd) (lixKZeroSet_compl_iff n k dd) q x

/-- **The local computation at each zero, over `K`.** -/
def KGenLocalNonzeroOf (K : Type) [Field K] (n k : ℕ) {dd : Fin ℓ → ℕ}
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    (u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd)) : Prop :=
  ∀ i : Fin (k + 1), ∃ B : Set (↥sphereOne × Gen.baseM n dd),
    (∀ j, j ≠ i → lixKZero n k dd j ∉ B) ∧
      (LIXKRelMV.restrictTo K (X := lixN n dd) B
          ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd)).hom
        ((lixKSRelOf K n k hGc hGu hGe (2 * lixRank n dd)).hom u) ≠ 0

/-- **(4) and (3) together over `K`**, from the local computation. -/
theorem exists_localSplit_ne_zero_kgenOf (K : Type) [Field K] (n k : ℕ) {dd : Fin ℓ → ℕ}
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    (u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd))
    (hlocal : KGenLocalNonzeroOf K n k hGc hGu hGe u) :
    ∃ xloc : ∀ i : Fin (k + 1), relCohomology K (lixN n dd)
        ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd),
      LocalSplit (fun i => lixKRhoOf K n k dd i (2 * lixRank n dd))
          ((lixKSRelOf K n k hGc hGu hGe (2 * lixRank n dd)).hom u) xloc ∧
        ∀ i, xloc i ≠ 0 := by
  obtain ⟨xloc, hs⟩ := exists_localSplit_kgenOf K n k dd (2 * lixRank n dd)
    ((lixKSRelOf K n k hGc hGu hGe (2 * lixRank n dd)).hom u)
  refine ⟨xloc, hs, fun i => ?_⟩
  obtain ⟨B, hB, hne⟩ := hlocal i
  exact LIXKRelMV.xloc_ne_zero_of_restrictTo_ne_zero (X := lixN n dd)
    (lixKZeroSet_compl_iff n k dd) (2 * lixRank n dd) hs i hB hne

end KGen

/-! Audited on every build. -/

#audit_axioms LIXKRelMV.exists_localSplitOf
#audit_axioms KGen.exists_localSplit_kgenOf
#audit_axioms KGen.exists_localSplit_ne_zero_kgenOf

end GroupApproximation.CharClass
