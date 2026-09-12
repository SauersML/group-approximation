import GroupApproximation.CharClass.LIXKGenStepCHalf
import GroupApproximation.CharClass.LIXKLocalRestrict
import GroupApproximation.Meta.AxiomGuard

/-!
# The split and the nonvanishing of the local classes, at rank `n`

Lane `lix-oddside` (lead ruling 2026-09-11: leaves (3) and (4) of `KGen.KZeroStepCData`,
in new `CharClass/LIXKGenLocal*` files over lix-oddside-n's bundle layer).

`KGen.KZeroStepCData n k dd hGc hGu hGe gamma` asks for a class `u` of the bundle pair, local
classes `xloc i` with

* (4) `LocalSplit (fun i => lixKRho n k dd i (2r)) (lixKSRel … u) xloc`,
* (3) `∀ i, xloc i ≠ 0`,
* (5) `lixJE u = lixPiStar gamma`.

(4) holds for every `u`: it is relative Mayer–Vietoris over the `k + 1` punctures
(`LIXKRelMV.exists_localSplit_two`).  (3) then reduces to a statement about `lixKSRel … u`
itself, read on sets that contain one zero and no other (`LIXKRelMV.xloc_ne_zero_of_restrictTo_ne_zero`):
that is `KGenLocalNonzero`, the local computation at each zero.

## Main declarations

* `exists_localSplit_kgen` — (4), for every class of the `k + 1`-punctured pair.
* `KGenLocalNonzero` — the local computation at each zero, named.
* `exists_localSplit_ne_zero_kgen` — (4) and (3) together, from `KGenLocalNonzero`.
* `kZeroStepCData_of_localNonzero` — `KZeroStepCData` from `KGenLocalNonzero` and (5).
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

theorem lixKZeroSet_compl_iff (n k : ℕ) (dd : Fin ℓ → ℕ) (y : ↥sphereOne × Gen.baseM n dd) :
    y ∈ ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd))
      ↔ ∀ i, y ≠ lixKZero n k dd i := by
  rw [Set.mem_compl_iff, mem_lixKZeroSet_iff, not_exists]

/-- **(4): the local split, for every class of the `k + 1`-punctured pair.** -/
theorem exists_localSplit_kgen (n k : ℕ) (dd : Fin ℓ → ℕ) (q : ℕ)
    (x : relCohomology (ZMod 2) (lixN n dd)
      ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q) :
    ∃ xloc : ∀ i : Fin (k + 1), relCohomology (ZMod 2) (lixN n dd)
        ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) q,
      LocalSplit (fun i => lixKRho n k dd i q) x xloc :=
  LIXKRelMV.exists_localSplit_two (X := lixN n dd) (lixKZero n k dd)
    (lixKZero_injective n k dd) (lixKZeroSet_compl_iff n k dd) q x

/-- **The local computation at each zero.**  For each zero `z_i` there is a set containing no
other zero on which `σ^* u` restricts nontrivially. -/
def KGenLocalNonzero (n k : ℕ) {dd : Fin ℓ → ℕ}
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    (u : relCohomology (ZMod 2) (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd)) : Prop :=
  ∀ i : Fin (k + 1), ∃ B : Set (↥sphereOne × Gen.baseM n dd),
    (∀ j, j ≠ i → lixKZero n k dd j ∉ B) ∧
      (LIXKRelMV.restrictTo (ZMod 2) (X := lixN n dd) B
          ((lixKZeroSet n k dd)ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd)).hom
        ((lixKSRel n k hGc hGu hGe (2 * lixRank n dd)).hom u) ≠ 0

/-- **(4) and (3) together**, from the local computation. -/
theorem exists_localSplit_ne_zero_kgen (n k : ℕ) {dd : Fin ℓ → ℕ}
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    (u : relCohomology (ZMod 2) (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd))
    (hlocal : KGenLocalNonzero n k hGc hGu hGe u) :
    ∃ xloc : ∀ i : Fin (k + 1), relCohomology (ZMod 2) (lixN n dd)
        ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd),
      LocalSplit (fun i => lixKRho n k dd i (2 * lixRank n dd))
          ((lixKSRel n k hGc hGu hGe (2 * lixRank n dd)).hom u) xloc ∧
        ∀ i, xloc i ≠ 0 := by
  obtain ⟨xloc, hs⟩ := exists_localSplit_kgen n k dd (2 * lixRank n dd)
    ((lixKSRel n k hGc hGu hGe (2 * lixRank n dd)).hom u)
  refine ⟨xloc, hs, fun i => ?_⟩
  obtain ⟨B, hB, hne⟩ := hlocal i
  exact LIXKRelMV.xloc_ne_zero_of_restrictTo_ne_zero (X := lixN n dd)
    (lixKZeroSet_compl_iff n k dd) (2 * lixRank n dd) hs i hB hne

/-- **`KZeroStepCData` from the local computation and the Thom-class link.** -/
theorem kZeroStepCData_of_localNonzero (n k : ℕ) {dd : Fin ℓ → ℕ}
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    {gamma : cohomologyZMod2 (lixN n dd) (2 * lixRank n dd)}
    (u : relCohomology (ZMod 2) (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd))
    (hlocal : KGenLocalNonzero n k hGc hGu hGe u)
    (hclass : (lixJE n hGc hGu (2 * lixRank n dd)).hom u
      = (lixPiStar n hGc hGu (2 * lixRank n dd)).hom gamma) :
    KZeroStepCData n k dd hGc hGu hGe gamma := by
  obtain ⟨xloc, hs, hx⟩ := exists_localSplit_ne_zero_kgen n k hGc hGu hGe u hlocal
  exact ⟨u, xloc, hs, hx, hclass⟩

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.exists_localSplit_kgen
#audit_axioms KGen.exists_localSplit_ne_zero_kgen
#audit_axioms KGen.kZeroStepCData_of_localNonzero

end GroupApproximation.CharClass
