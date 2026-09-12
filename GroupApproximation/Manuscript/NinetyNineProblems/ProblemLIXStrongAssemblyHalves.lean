import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIXStrongAssembly
import GroupApproximation.CharClass.LIXLemmaTwoGenGlue
import GroupApproximation.Meta.AxiomGuard

/-!
# STW Problem LIX, strengthened: Lemma 2 for the agreed family from its two halves

`ProblemLIXStrongAssembly.lean` states the stronger theorem over Lemma 2 at
`powersSections n k = fun j => CharClass.KGen.bVecK n (k - 1)`.  The rank-`n` glue of Lemma 2
(`CharClass/LIXLemmaTwoGenGlue.lean`, `lix-evenside-n`) proves exactly that conclusion, per prime,
from the two halves of the argument:

* `Gen.lemmaTwoFor_powers_of_halves` — from a Step C half (`StepCHalf`, the geometric half owned by
  `lix-oddside` / `lix-oddside-n`) and a Step D half (`StepDHalf`) sharing one top-class map;
* `Gen.lemmaTwoFor_powers_of_stepC_modP` — the same with Step D discharged by the mod-`p` data of
  `CharClass/LIXStepDGenHalf.lean`, so that only Step C and the `ModPStepDData` producers remain.

Step A enters through `Gen.hasStepAUnitary_of_continuousMvNEquiv`
(`CharClass/LIXLemmaTwoGenStepA.lean`), inside the glue.

This file restates those two arrows at `powersSections`, and assembles the stronger theorem over
them, so that the day Step C and the `ModPStepDData` producers land, the endpoint is one application
of the theorems below.
-/

namespace GroupApproximation
namespace NinetyNineProblems

open scoped Matrix
open CharClass CharClass.Gen

noncomputable section

/-- **Lemma 2 at the agreed family, for the exponents a fixed prime misses**, is the glue's
per-stage conclusion read through `powersSections`. -/
theorem lemmaTwoHoldsForSections_powersSections_iff_forall (n p : ℕ) :
    (∀ k : ℕ, ¬ p ∣ k → LemmaTwoHoldsForSections n (powersSections n k)) ↔
      ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
        LIX.Gen.LemmaTwoFor n (LIX.Gen.lixDD n j) (KGen.bVecK n (k - 1)) :=
  Iff.rfl

/-- **From the two halves**: a Step C half and a Step D half sharing one top-class map give
Lemma 2 at `powersSections n k` for every exponent `k` the prime `p` misses. -/
theorem lemmaTwoHoldsForSections_powersSections_of_halves (n p : ℕ) {K : ℕ → Type*}
    [∀ j, Zero (K j)]
    (topClass : ∀ j : ℕ, (↥sphereOne × baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
          (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j)) ℂ) → K j)
    (hC : ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
      StepCHalf n (LIX.Gen.lixDD n j) (KGen.bVecK n (k - 1)) (topClass j))
    (hD : ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ, StepDHalf n (LIX.Gen.lixDD n j) (topClass j)) :
    ∀ k : ℕ, ¬ p ∣ k → LemmaTwoHoldsForSections n (powersSections n k) :=
  (lemmaTwoHoldsForSections_powersSections_iff_forall n p).mpr
    (lemmaTwoFor_powers_of_halves n p topClass hC hD)

/-- **From Step C and the mod-`p` data**: with Step D discharged by `LIXStepDGenHalf`, Lemma 2
at `powersSections n k` for every exponent `k` a prime `p ∣ n` misses needs only the Step C half
and the `ModPStepDData` producers. -/
theorem lemmaTwoHoldsForSections_powersSections_of_stepC_modP (n p : ℕ) (hp : p.Prime)
    (hn : 1 ≤ n) (hpn : p ∣ n)
    {R H : ℕ → Type*} [∀ j, CommRing (R j)] [∀ j, CommRing (H j)] [∀ j, ExpChar (R j) p]
    (γfun : ∀ j : ℕ, (↥sphereOne × baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j))
          (VIdx n (LIX.Gen.lixDD n j) ⊕ VIdx n (LIX.Gen.lixDD n j)) ℂ) → ℕ → H j)
    (data : ∀ (j : ℕ) (G : baseM n (LIX.Gen.lixDD n j) →
        Matrix (VIdx n (LIX.Gen.lixDD n j)) (VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ m, IsCornerUnitary (Vmat n m) (G m)) →
      ModPStepDData n p (LIX.Gen.lixDD n j) (R j) (H j)
        (γfun j (mappingTorus (Vmat n) G circHoriz circHeight)))
    (hC : ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
      StepCHalf n (LIX.Gen.lixDD n j) (KGen.bVecK n (k - 1))
        (fun W => γfun j W ((∑ i, LIX.Gen.lixDD n j i) + (n + 1)))) :
    ∀ k : ℕ, ¬ p ∣ k → LemmaTwoHoldsForSections n (powersSections n k) :=
  (lemmaTwoHoldsForSections_powersSections_iff_forall n p).mpr
    (lemmaTwoFor_powers_of_stepC_modP n p hp hn hpn γfun data hC)

/-- **The stronger theorem over the per-prime glue conclusion.**  `lix-tower`'s arrow at
`powersSections n`, and for every prime `p ∣ n` the glue's conclusion at the exponents `p` misses
(from `lemmaTwoFor_powers_of_stepC_modP` or `lemmaTwoFor_powers_of_halves`), give the power
witness. -/
theorem exists_isSimpleRing_separable_hasK1InjPowerWitness_of_powersSections_glue (n : ℕ)
    (hn : 2 ≤ n) (hcor4 : Corollary4Powers n (powersSections n))
    (hglue : ∀ p : ℕ, p.Prime → p ∣ n → ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
      LIX.Gen.LemmaTwoFor n (LIX.Gen.lixDD n j) (KGen.bVecK n (k - 1))) :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleRing A ∧ TopologicalSpace.SeparableSpace A ∧
        HasK1InjPowerWitness A n :=
  exists_isSimpleRing_separable_hasK1InjPowerWitness_of_powersSections n hn hcor4 hglue

end

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_axioms lemmaTwoHoldsForSections_powersSections_iff_forall
#audit_axioms lemmaTwoHoldsForSections_powersSections_of_halves
#audit_axioms lemmaTwoHoldsForSections_powersSections_of_stepC_modP
#audit_axioms exists_isSimpleRing_separable_hasK1InjPowerWitness_of_powersSections_glue
