import GroupApproximation.CharClass.LIXStepDGenChernSplit
import GroupApproximation.CharClass.LIXStepDGenSliceV
import GroupApproximation.CharClass.LIXStepDGenSplit
import GroupApproximation.CharClass.CohomologyKunnethLixN
import GroupApproximation.CharClass.LIXLemmaTwoGenTwo
import GroupApproximation.Meta.AxiomGuard

/-!
# The mod-2 Step D data of the rank-`n` mapping torus, at every stage

Lane `lx-slice2` of the LIX strongest swarm.  This file produces the binder `data` of
`Gen.lemmaTwoFor_powers_two_lixChernOf` (`CharClass/LIXLemmaTwoGenTwo.lean`): a
`Gen.WuStepDData` for the mod-2 Chern classes of the mapping torus of every continuous
corner unitary, at every stage `j` of the rank-`n` tower.

Every field is a theorem:

| field | source |
|---|---|
| `tx_inj`, `gamma_eq`, `sq_b` | `KnLix.tx_inj`, `KnLix.gamma_split_mappingTorus` (lx-kunneth) |
| `split` | `Gen.hasSplitting_lixN` |
| `gen`, `slice` | `LH.sliceGen`; the section `Gen.lixSliceN` at the south pole, on which the circle class dies, and `Gen.map_lixSliceN_lixChernOf_eq_sliceClass` |

The objects are `Y j = ∏ᵢ ℂP^{dᵢ}`, `S₁ j = S¹`, `Sodd j = S^{2n+1}` with lx-kunneth's three
projections and the vendored top classes of the two spheres.  The only hypothesis on the rank
is `NeZero n`, which gives the positivity of every `dᵢ = 2^i · n` that `LH.sliceGen` needs.

## Main declarations

* `Gen.lixSliceN_comp_prY`, `Gen.lixSliceN_comp_prS1` — the slice sections the Künneth
  projection to `Y` and is constant on the circle.
* `Gen.wuStepDData_lixN` — **the data**, at every stage and every corner unitary.
* `Gen.lemmaTwoFor_powers_two_of_localData` — Lemma 2 for the degree-`k` family at `p = 2`, with
  the Step D data discharged: the one remaining input is Step C's local data.
-/

noncomputable section

namespace GroupApproximation
namespace CharClass
namespace Gen

open CategoryTheory
open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

/-- The slice sections the projection to the projective factors. -/
theorem lixSliceN_comp_prY (n : ℕ) (dd : Fin ℓ → ℕ) (p1 : ↥sphereOne)
    (q : ↥(unitVectors (Fin (n + 1)))) :
    lixSliceN n dd p1 q ≫ KnLix.prY n dd = 𝟙 (TopCat.of (baseY dd)) := by
  apply TopCat.Hom.ext
  ext y
  rfl

/-- The slice is constant on the circle factor. -/
theorem lixSliceN_comp_prS1 (n : ℕ) (dd : Fin ℓ → ℕ) (p1 : ↥sphereOne)
    (q : ↥(unitVectors (Fin (n + 1)))) :
    lixSliceN n dd p1 q ≫ KnLix.prS1 n dd
      = cmap (ContinuousMap.const (baseY dd) (p1 : Sphere 1)) := by
  apply TopCat.Hom.ext
  ext y
  rfl

/-- **The mod-2 Step D data of the rank-`n` mapping torus**, at stage `j`, for every continuous
corner unitary `G`.  No field is a hypothesis. -/
def wuStepDData_lixN (n : ℕ) [NeZero n] (j : ℕ)
    (G : baseM n (LIX.Gen.lixDD n j) →
      Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ)
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat n m) (G m)) :
    WuStepDData n (LIX.Gen.lixDD n j) (KnLix.prY n (LIX.Gen.lixDD n j))
      (KnLix.prS1 n (LIX.Gen.lixDD n j)) (KnLix.prSodd n (LIX.Gen.lixDD n j))
      (sphereTopClass 1 (by omega)) (sphereTopClass (2 * n + 1) (by omega))
      (KGen.lixChernOf n (KGen.lixChern n (LIX.Gen.lixDD n j))
        (mappingTorus (Vmat n) G circHoriz circHeight)) :=
  WuStepDData.ofSection n (LIX.Gen.lixDD n j)
    (KnLix.gamma_split_mappingTorus n (LIX.Gen.lixDD n j) hGc hGu)
    (KnLix.tx_inj n (LIX.Gen.lixDD n j))
    (hasSplitting_lixN n G hGc hGu)
    (lixSliceN n (LIX.Gen.lixDD n j) southPole (negELast n))
    (lixSliceN_comp_prY n (LIX.Gen.lixDD n j) southPole (negELast n))
    (map_tClass_eq_zero_of_const (sphereTopClass 1 (by omega))
      (lixSliceN n (LIX.Gen.lixDD n j) southPole (negELast n)) (southPole : Sphere 1)
      (lixSliceN_comp_prS1 n (LIX.Gen.lixDD n j) southPole (negELast n)))
    (LH.sliceGen (LIX.Gen.lixDD n j) (LIX.Gen.lixDD_pos n j))
    (fun q => map_lixSliceN_lixChernOf_eq_sliceClass n (LIX.Gen.lixDD_pos n j) hGc hGu
      (negELast n) q)

/-- The data exists, in the form an existential endpoint consumes. -/
theorem nonempty_wuStepDData_lixN (n : ℕ) [NeZero n] (j : ℕ)
    (G : baseM n (LIX.Gen.lixDD n j) →
      Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ)
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat n m) (G m)) :
    Nonempty (WuStepDData n (LIX.Gen.lixDD n j) (KnLix.prY n (LIX.Gen.lixDD n j))
      (KnLix.prS1 n (LIX.Gen.lixDD n j)) (KnLix.prSodd n (LIX.Gen.lixDD n j))
      (sphereTopClass 1 (by omega)) (sphereTopClass (2 * n + 1) (by omega))
      (KGen.lixChernOf n (KGen.lixChern n (LIX.Gen.lixDD n j))
        (mappingTorus (Vmat n) G circHoriz circHeight))) :=
  ⟨wuStepDData_lixN n j G hGc hGu⟩

/-- **Lemma 2 for the degree-`k` family at `p = 2`, with Step D discharged.**  For even `n ≥ 2`,
every odd exponent and every stage, from Step C's local data alone. -/
theorem lemmaTwoFor_powers_two_of_localData (n : ℕ) [NeZero n] (hn : Even n) (hn2 : 2 ≤ n)
    (hloc : ∀ (e : ℕ), Odd e → ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ)
      (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat n m) (G m))
      (hGe : ∀ m, G m *ᵥ Sum.elim (KGen.aVecK n m) 0 = Sum.elim (KGen.bVecK n (e - 1) m) 0),
      KGen.KZeroLocalData n (e - 1) (LIX.Gen.lixDD n j) hGc hGu hGe) :
    ∀ k : ℕ, ¬ 2 ∣ k → ∀ j : ℕ,
      LIX.Gen.LemmaTwoFor n (LIX.Gen.lixDD n j) (KGen.bVecK n (k - 1)) :=
  lemmaTwoFor_powers_two_lixChernOf n hn hn2
    (fun j => KnLix.prY n (LIX.Gen.lixDD n j)) (fun j => KnLix.prS1 n (LIX.Gen.lixDD n j))
    (fun j => KnLix.prSodd n (LIX.Gen.lixDD n j)) Wu.cartanTotal
    (fun _ => hasSphereCohomology_sphere 1 (by omega))
    (fun _ => hasSphereCohomology_sphere (2 * n + 1) (by omega))
    (fun _ => sphereTopClass 1 (by omega)) (fun _ => sphereTopClass (2 * n + 1) (by omega))
    (fun j G hGc hGu => wuStepDData_lixN n j G hGc hGu) hloc

end Gen

/-! Audited on every build. -/

#audit_axioms Gen.wuStepDData_lixN
#audit_axioms Gen.nonempty_wuStepDData_lixN
#audit_axioms Gen.lemmaTwoFor_powers_two_of_localData

end CharClass
end GroupApproximation

end
