import GroupApproximation.CharClass.LIXKGenAgree
import GroupApproximation.CharClass.LIXKGenLocalSplitOf
import GroupApproximation.CharClass.LIXKGenOfStepC
import GroupApproximation.Meta.AxiomGuard

/-!
# The `k`-zero Step C over a field from two inputs: local nonvanishing, and the Thom identity

Lane `lx-stepcK-agree`.

`CharClass/LIXKGenOfStepC.lean` closes the Step C half over a field `K` from the open data
`KGen.KZeroStepCDataOf`: a relative class `u`, a split of its section pullback into local classes, their
nonvanishing, their AGREEMENT, and `jE u = π^* γ`.  Two of those fields are now theorems for every `u`:

* the split, `KGen.exists_localSplit_kgenOf` (finite-puncture Mayer–Vietoris over a field);
* the agreement, `KGen.localClassesAgree_of_localSplitOf` (`CharClass/LIXKGenAgree.lean`, the rotation
  argument).

What remains is the local nonvanishing at every zero (`KGen.KGenLocalNonzeroOf`, lane `lx-stepcK-local`)
and the Thom identity `jE u = π^* γ`.

## Main declarations

* `KGen.kZeroStepCDataOf_of_localNonzeroOf` — the open data from the two inputs.
* `KGen.stepCHalf_of_localNonzeroOf` — **the Step C half over `K`, for `p ∤ k + 1`**, from the two inputs.
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

/-- **The open data of the `k`-zero Step C over a field, from the local nonvanishing of `u` and the Thom
identity.**  The split and the agreement of the local classes are theorems. -/
theorem kZeroStepCDataOf_of_localNonzeroOf (K : Type) [Field K] (n k : ℕ) (dd : Fin ℓ → ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    {gamma : Hmod K (lixN n dd) (2 * lixRank n dd)}
    (u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd))
    (hlocal : KGenLocalNonzeroOf K n k hGc hGu hGe u)
    (hclass : (lixJEOf K n hGc hGu (2 * lixRank n dd)).hom u
      = (lixPiStarOf K n hGc hGu (2 * lixRank n dd)).hom gamma) :
    KZeroStepCDataOf K n k dd hGc hGu hGe gamma := by
  obtain ⟨xloc, hsplit, hx⟩ := exists_localSplit_ne_zero_kgenOf K n k hGc hGu hGe u hlocal
  exact ⟨u, xloc, _, hsplit, hx,
    localClassesAgree_of_localSplitOf K n k dd hGc hGu hGe (2 * lixRank n dd) u xloc hsplit, hclass⟩

/-- **The Step C half over a field, for the `k`-section with `p ∤ k + 1`**, from a relative class of every
corner unitary's bundle pair that is locally nonzero at every zero and restricts to `π^*` of the top
class. -/
theorem stepCHalf_of_localNonzeroOf (K : Type) [Field K] (n k : ℕ)
    (hk : ((k + 1 : ℕ) : K) ≠ 0) (dd : Fin ℓ → ℕ) (hdd : ∀ j, 0 < dd j)
    (topClass : (↥sphereOne × Gen.baseM n dd →
      Matrix (Gen.VIdx n dd ⊕ Gen.VIdx n dd) (Gen.VIdx n dd ⊕ Gen.VIdx n dd) ℂ) →
        Hmod K (lixN n dd) (2 * lixRank n dd))
    (hdata : ∀ (G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ)
      (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
      (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0),
      ∃ u : relCohomology K (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
          (2 * lixRank n dd),
        KGenLocalNonzeroOf K n k hGc hGu hGe u ∧
          (lixJEOf K n hGc hGu (2 * lixRank n dd)).hom u
            = (lixPiStarOf K n hGc hGu (2 * lixRank n dd)).hom
                (topClass (mappingTorus (Gen.Vmat n) G circHoriz circHeight))) :
    Gen.StepCHalf n dd (bVecK n k) topClass :=
  stepCHalf_of_kZeroStepCDataOf K n k hk dd hdd topClass fun G hGc hGu hGe => by
    obtain ⟨u, hl, hc⟩ := hdata G hGc hGu hGe
    exact kZeroStepCDataOf_of_localNonzeroOf K n k dd hGc hGu hGe u hl hc

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.kZeroStepCDataOf_of_localNonzeroOf
#audit_axioms KGen.stepCHalf_of_localNonzeroOf

end GroupApproximation.CharClass
