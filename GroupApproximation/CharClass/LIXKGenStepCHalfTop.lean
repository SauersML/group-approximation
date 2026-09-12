import GroupApproximation.CharClass.LIXKGenHclass
import GroupApproximation.CharClass.LIXKGenStepCHalf
import GroupApproximation.Meta.AxiomGuard

/-!
# The Step C half at rank `n` and `p = 2`, at the top Chern class in `TotalH`

Lane `lix-oddside-n` (leaf (5) discharged into the assembly, and the `γfun` adapter).

`CharClass/LIXKGenStepCHalf.lean` states `Gen.StepCHalf n dd (bVecK n k) topClass` over
`KGen.KZeroStepCData`, whose `hclass` field asks for a relative class `u` restricting to
`π^* gamma`.  With `u := KGen.lixThomClassTerm n hGc hGu` and `gamma` the top Chern class,
that field is `KGen.lixHclass n` (`CharClass/LIXKGenHclass.lean`), so the only remaining data
are the local classes: `KGen.KZeroLocalData`.

The consumers (`Gen.stepDHalf_of_wu`, `Gen.lemmaTwoFor_of_halves`) speak about a class
`γfun W ((∑ⱼ dⱼ) + (n + 1))` in a ring `TotalH N`; the natural `γfun` is
`fun W k => KGen.lixChernOf n (KGen.lixChern n dd) W k`, and on a mapping torus it is
`TotalH.of` of the degreewise class (`KGen.lixChernOf_mappingTorus`), which is nonzero iff the
degreewise class is (`ne_zero_of_degree_ne_zero`).  So the Step C half below is stated at exactly
that `topClass`, on the nose.

## Main declarations

* `KGen.KZeroLocalData` — local classes splitting the section pullback of the Thom class, all
  nonzero: leaves (3) and (4), lane `lix-oddside`.
* `KGen.kZeroStepCData_of_kZeroLocalData` — `KZeroStepCData` at the top Chern class.
* `KGen.stepCHalf_two_lixChernOf` — **`Gen.StepCHalf n dd (bVecK n k)` at
  `fun W => lixChernOf n (lixChern n dd) W ((∑ⱼ dⱼ) + (n + 1))`**, for `k + 1` odd.
* `KGen.stepCHalf_two_powers_lixChernOf` — at every stage `j` and every odd exponent `e`, for
  `bVecK n (e − 1)`.
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

/-- **The local data of the `k`-zero Step C once the Thom class is fixed**: local classes at the
`k+1` zeros splitting the section pullback of `lixThomClassTerm`, all nonzero. -/
def KZeroLocalData (n k : ℕ) (dd : Fin ℓ → ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0) : Prop :=
  ∃ xloc : ∀ i : Fin (k + 1), relCohomology (ZMod 2) (lixN n dd)
      ({lixKZero n k dd i}ᶜ : Set (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd),
    LocalSplit (fun i => lixKRho n k dd i (2 * lixRank n dd))
        ((lixKSRel n k hGc hGu hGe (2 * lixRank n dd)).hom (lixThomClassTerm n hGc hGu)) xloc ∧
      ∀ i, xloc i ≠ 0

/-- **`KZeroStepCData` at the top Chern class, from the local data alone**: `hclass` is
`lixHclass`. -/
theorem kZeroStepCData_of_kZeroLocalData (n k : ℕ) (dd : Fin ℓ → ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0)
    (h : KZeroLocalData n k dd hGc hGu hGe) :
    KZeroStepCData n k dd hGc hGu hGe
      (lixChern n dd (mappingTorus (Gen.Vmat n) G circHoriz circHeight)
        (continuous_mappingTorus_lix n hGc) (isStarProjection_mappingTorus_lix n hGu)
        (lixRank n dd)) := by
  obtain ⟨xloc, hsplit, hx⟩ := h
  unfold KZeroStepCData
  exact ⟨lixThomClassTerm n hGc hGu, xloc, hsplit, hx, lixHclass n hGc hGu _ _⟩

/-- **The Step C half at `p = 2`, at the top Chern class in `TotalH`.** -/
theorem stepCHalf_two_lixChernOf (n k : ℕ) (hodd : Odd (k + 1)) (dd : Fin ℓ → ℕ)
    (hdd : ∀ j, 0 < dd j)
    (hdata : ∀ (G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ)
      (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
      (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n k m) 0),
      KZeroLocalData n k dd hGc hGu hGe) :
    Gen.StepCHalf n dd (bVecK n k)
      (fun W => lixChernOf n (lixChern n dd) W ((∑ j, dd j) + (n + 1))) := by
  intro G hGc hGu hGe
  show lixChernOf n (lixChern n dd) (mappingTorus (Gen.Vmat n) G circHoriz circHeight)
    (lixRank n dd) ≠ 0
  rw [lixChernOf_mappingTorus n (lixChern n dd) hGc hGu]
  refine ne_zero_of_degree_ne_zero ?_
  obtain ⟨_u, _xloc, hsplit, hx, hclass⟩ :=
    kZeroStepCData_of_kZeroLocalData n k dd hGc hGu hGe (hdata G hGc hGu hGe)
  exact lixK_topClass_ne_zero_two_odd n k hodd hdd hGc hGu hGe (absEquiv_lixN n dd hdd)
    (chart := fun _ => relCohomology (ZMod 2) (TopCat.of (Fin (lixRank n dd) → ℂ))
      (puncturedSet (lixRank n dd)) (2 * lixRank n dd))
    (fun i => lixKRelModelIso n k dd i (2 * lixRank n dd)) (fun _ => Iso.refl _) hsplit hx
    hclass

/-- **The exponent-facing form** at every stage `j` and every odd exponent `e`, at the section
`bVecK n (e − 1)` and the class `γfun W ((∑ i, lixDD n j i) + (n + 1))` the glue consumes. -/
theorem stepCHalf_two_powers_lixChernOf (n : ℕ) [NeZero n] (e : ℕ) (he : Odd e) (j : ℕ)
    (hdata : ∀ (G : Gen.baseM n (LIX.Gen.lixDD n j) →
        Matrix (Gen.VIdx n (LIX.Gen.lixDD n j)) (Gen.VIdx n (LIX.Gen.lixDD n j)) ℂ)
      (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
      (hGe : ∀ m, G m *ᵥ Sum.elim (aVecK n m) 0 = Sum.elim (bVecK n (e - 1) m) 0),
      KZeroLocalData n (e - 1) (LIX.Gen.lixDD n j) hGc hGu hGe) :
    Gen.StepCHalf n (LIX.Gen.lixDD n j) (bVecK n (e - 1))
      (fun W => lixChernOf n (lixChern n (LIX.Gen.lixDD n j)) W
        ((∑ i, LIX.Gen.lixDD n j i) + (n + 1))) := by
  have hodd : Odd (e - 1 + 1) := by
    rw [Nat.sub_add_cancel he.pos]
    exact he
  exact stepCHalf_two_lixChernOf n (e - 1) hodd (LIX.Gen.lixDD n j) (LIX.Gen.lixDD_pos n j)
    hdata

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.kZeroStepCData_of_kZeroLocalData
#audit_axioms KGen.stepCHalf_two_lixChernOf
#audit_axioms KGen.stepCHalf_two_powers_lixChernOf

end GroupApproximation.CharClass
