import GroupApproximation.CharClass.LIXLemmaTwoGenGlue
import GroupApproximation.CharClass.LIXKGenStepCHalfTop

/-!
# Lemma 2 at rank `n` and `p = 2` for the degree-`k` family, with one class on both halves

Lane `lix-evenside-n` of the STW Problem LIX strengthening programme
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.6; lead's relay of 2026-09-11 from
`lix-oddside-n`).

`Gen.lemmaTwoFor_of_halves` needs ONE class `topClass` on both halves.  `lix-oddside-n`'s Step C
half (`CharClass/LIXKGenStepCHalfTop.lean`, `KGen.stepCHalf_two_powers_lixChernOf`) is stated at

```text
topClass j := fun W => KGen.lixChernOf n (KGen.lixChern n (lixDD n j)) W ((∑ i, lixDD n j i) + (n + 1))
```

in the mod-2 ring `TotalH (KGen.lixN n (lixDD n j))`.  This lane's Step D half at `p = 2`,
`Gen.stepDHalf_powers_of_wu` (`CharClass/LIXStepDGenHalf.lean`), is stated for an arbitrary
`γfun` and base `N`; at `N j := KGen.lixN n (lixDD n j)` and
`γfun j W k := KGen.lixChernOf n (KGen.lixChern n (lixDD n j)) W k` its `topClass` is the same
term, so the two halves compose with no bridge.

## Main result

* `Gen.lemmaTwoFor_powers_two_lixChernOf` — for even `n ≥ 2`, every odd exponent `k` and every
  stage `j`, `LIX.Gen.LemmaTwoFor n (lixDD n j) (KGen.bVecK n (k − 1))`, from the local data of
  Step C (`KGen.KZeroLocalData`) and the mod-2 Step D data (`Gen.WuStepDData`) at `lixN`.
-/

noncomputable section

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59

namespace Gen

/-- **Lemma 2 for the degree-`k` family at `p = 2`, at every stage, one class on both halves.**
The residual inputs are exactly `lix-oddside-n`'s local data and the mod-2 Step D data of the
top Chern class `KGen.lixChernOf n (KGen.lixChern n (lixDD n j))`. -/
theorem lemmaTwoFor_powers_two_lixChernOf (n : ℕ) [NeZero n] (hn : Even n) (hn2 : 2 ≤ n)
    {Y S₁ Sodd : ℕ → TopCat.{0}}
    (pY : ∀ j, KGen.lixN n (LIX.Gen.lixDD n j) ⟶ Y j)
    (q₁ : ∀ j, KGen.lixN n (LIX.Gen.lixDD n j) ⟶ S₁ j)
    (qodd : ∀ j, KGen.lixN n (LIX.Gen.lixDD n j) ⟶ Sodd j)
    (hC : Wu.CartanTotal)
    (hS₁ : ∀ j, HasSphereCohomology (S₁ j) 1)
    (hSodd : ∀ j, HasSphereCohomology (Sodd j) (2 * n + 1))
    (σ₁ : ∀ j, Hmod2 (S₁ j) 1) (σodd : ∀ j, Hmod2 (Sodd j) (2 * n + 1))
    (data : ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ m, IsCornerUnitary (Vmat n m) (G m)) →
      WuStepDData n (LIX.Gen.lixDD n j) (pY j) (q₁ j) (qodd j) (σ₁ j) (σodd j)
        (KGen.lixChernOf n (KGen.lixChern n (LIX.Gen.lixDD n j))
          (mappingTorus (Vmat n) G circHoriz circHeight)))
    (hloc : ∀ (e : ℕ), Odd e → ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ)
      (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat n m) (G m))
      (hGe : ∀ m, G m *ᵥ Sum.elim (KGen.aVecK n m) 0 = Sum.elim (KGen.bVecK n (e - 1) m) 0),
      KGen.KZeroLocalData n (e - 1) (LIX.Gen.lixDD n j) hGc hGu hGe) :
    ∀ k : ℕ, ¬ 2 ∣ k → ∀ j : ℕ,
      LIX.Gen.LemmaTwoFor n (LIX.Gen.lixDD n j) (KGen.bVecK n (k - 1)) :=
  lemmaTwoFor_powers_of_halves n 2
    (fun j W => KGen.lixChernOf n (KGen.lixChern n (LIX.Gen.lixDD n j)) W
      ((∑ i, LIX.Gen.lixDD n j i) + (n + 1)))
    (fun k hk j => KGen.stepCHalf_two_powers_lixChernOf n k (Nat.odd_iff.mpr (by omega)) j
      (hloc k (Nat.odd_iff.mpr (by omega)) j))
    (stepDHalf_powers_of_wu n hn hn2 pY q₁ qodd hC hS₁ hSodd σ₁ σodd
      (fun j W k => KGen.lixChernOf n (KGen.lixChern n (LIX.Gen.lixDD n j)) W k) data)

end Gen

#audit_axioms Gen.lemmaTwoFor_powers_two_lixChernOf

end CharClass
end GroupApproximation

end
