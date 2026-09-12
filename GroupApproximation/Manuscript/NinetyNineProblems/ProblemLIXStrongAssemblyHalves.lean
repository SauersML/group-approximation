import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIXStrongAssemblyCor4
import GroupApproximation.CharClass.LIXLemmaTwoGenGlue
import GroupApproximation.Meta.AxiomGuard

/-!
# STW Problem LIX, strengthened: Lemma 2 at the powers from its two halves

`ProblemLIXStrongAssemblyCor4.lean` reduces the stronger theorem to one named input,
`LemmaTwoHoldsAtPowers n`: Lemma 2 at `powersSections n k = fun j => CharClass.KGen.bVecK n (k - 1)`
for every exponent `k` some prime dividing `n` misses.  The rank-`n` glue of Lemma 2
(`CharClass/LIXLemmaTwoGenGlue.lean`, `lix-evenside-n`) proves that conclusion, prime by prime,
from the two halves of the argument:

* `Gen.lemmaTwoFor_powers_of_halves` — from a Step C half (`StepCHalf`, owned by `lix-oddside` /
  `lix-oddside-n`) and a Step D half (`StepDHalf`) sharing one top-class map;
* `Gen.lemmaTwoFor_powers_of_stepC_modP` — the same with Step D discharged by the mod-`p` data of
  `CharClass/LIXStepDGenHalf.lean`, so that only Step C and the `ModPStepDData` producers remain.

Step A enters through `Gen.hasStepAUnitary_of_continuousMvNEquiv`
(`CharClass/LIXLemmaTwoGenStepA.lean`), inside the glue.

This file restates the two arrows at `powersSections` and assembles the stronger theorem over the
per-prime glue conclusion.  Every glue name is written with its full namespace: `CharClass` also
declares rank-two `VIdx`, `baseM` and `Vmat`, so opening both namespaces would make them ambiguous.
-/

namespace GroupApproximation
namespace NinetyNineProblems

open scoped Matrix

noncomputable section

/-- **Lemma 2 at the agreed family, for the exponents a fixed prime misses**, is the glue's
per-stage conclusion read through `powersSections`. -/
theorem lemmaTwoHoldsForSections_powersSections_iff_forall (n p : ℕ) :
    (∀ k : ℕ, ¬ p ∣ k → LemmaTwoHoldsForSections n (powersSections n k)) ↔
      ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
        LIX.Gen.LemmaTwoFor n (LIX.Gen.lixDD n j) (CharClass.KGen.bVecK n (k - 1)) :=
  Iff.rfl

/-- **From the two halves**: a Step C half and a Step D half sharing one top-class map give
Lemma 2 at `powersSections n k` for every exponent `k` the prime `p` misses. -/
theorem lemmaTwoHoldsForSections_powersSections_of_halves (n p : ℕ) {K : ℕ → Type*}
    [∀ j, Zero (K j)]
    (topClass : ∀ j : ℕ, (↥CharClass.sphereOne × CharClass.Gen.baseM n (LIX.Gen.lixDD n j) →
        Matrix (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j) ⊕ CharClass.Gen.VIdx n (LIX.Gen.lixDD n j))
          (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j) ⊕ CharClass.Gen.VIdx n (LIX.Gen.lixDD n j)) ℂ) →
        K j)
    (hC : ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
      CharClass.Gen.StepCHalf n (LIX.Gen.lixDD n j) (CharClass.KGen.bVecK n (k - 1)) (topClass j))
    (hD : ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
      CharClass.Gen.StepDHalf n (LIX.Gen.lixDD n j) (topClass j)) :
    ∀ k : ℕ, ¬ p ∣ k → LemmaTwoHoldsForSections n (powersSections n k) :=
  (lemmaTwoHoldsForSections_powersSections_iff_forall n p).mpr
    (CharClass.Gen.lemmaTwoFor_powers_of_halves n p topClass hC hD)

/-- **From Step C and the mod-`p` data**: with Step D discharged by `LIXStepDGenHalf`, Lemma 2
at `powersSections n k` for every exponent `k` a prime `p ∣ n` misses needs only the Step C half
and the `ModPStepDData` producers. -/
theorem lemmaTwoHoldsForSections_powersSections_of_stepC_modP (n p : ℕ) (hp : p.Prime)
    (hn : 1 ≤ n) (hpn : p ∣ n)
    {R H : ℕ → Type*} [∀ j, CommRing (R j)] [∀ j, CommRing (H j)] [∀ j, ExpChar (R j) p]
    (γfun : ∀ j : ℕ, (↥CharClass.sphereOne × CharClass.Gen.baseM n (LIX.Gen.lixDD n j) →
        Matrix (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j) ⊕ CharClass.Gen.VIdx n (LIX.Gen.lixDD n j))
          (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j) ⊕ CharClass.Gen.VIdx n (LIX.Gen.lixDD n j)) ℂ) →
        ℕ → H j)
    (data : ∀ (j : ℕ) (G : CharClass.Gen.baseM n (LIX.Gen.lixDD n j) →
        Matrix (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j))
          (CharClass.Gen.VIdx n (LIX.Gen.lixDD n j)) ℂ), Continuous G →
      (∀ m, CharClass.IsCornerUnitary (CharClass.Gen.Vmat n m) (G m)) →
      CharClass.Gen.ModPStepDData n p (LIX.Gen.lixDD n j) (R j) (H j)
        (γfun j (CharClass.mappingTorus (CharClass.Gen.Vmat n) G CharClass.circHoriz
          CharClass.circHeight)))
    (hC : ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
      CharClass.Gen.StepCHalf n (LIX.Gen.lixDD n j) (CharClass.KGen.bVecK n (k - 1))
        (fun W => γfun j W ((∑ i, LIX.Gen.lixDD n j i) + (n + 1)))) :
    ∀ k : ℕ, ¬ p ∣ k → LemmaTwoHoldsForSections n (powersSections n k) :=
  (lemmaTwoHoldsForSections_powersSections_iff_forall n p).mpr
    (CharClass.Gen.lemmaTwoFor_powers_of_stepC_modP n p hp hn hpn γfun data hC)

/-- **The one remaining input, from the per-prime glue conclusion.** -/
theorem lemmaTwoHoldsAtPowers_of_glue (n : ℕ)
    (hglue : ∀ p : ℕ, p.Prime → p ∣ n → ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
      LIX.Gen.LemmaTwoFor n (LIX.Gen.lixDD n j) (CharClass.KGen.bVecK n (k - 1))) :
    LemmaTwoHoldsAtPowers n :=
  (lemmaTwoHoldsAtPowers_iff n).mpr hglue

/-- **The stronger theorem over the per-prime glue conclusion**, with Corollary 4 discharged. -/
theorem exists_isSimpleRing_separable_hasK1InjPowerWitness_of_glue (n : ℕ) (hn : 2 ≤ n)
    (hglue : ∀ p : ℕ, p.Prime → p ∣ n → ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
      LIX.Gen.LemmaTwoFor n (LIX.Gen.lixDD n j) (CharClass.KGen.bVecK n (k - 1))) :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleRing A ∧ TopologicalSpace.SeparableSpace A ∧
        HasK1InjPowerWitness A n :=
  exists_isSimpleRing_separable_hasK1InjPowerWitness_of_lemmaTwoHoldsAtPowers n hn
    (lemmaTwoHoldsAtPowers_of_glue n hglue)

end

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_axioms lemmaTwoHoldsForSections_powersSections_iff_forall
#audit_axioms lemmaTwoHoldsForSections_powersSections_of_halves
#audit_axioms lemmaTwoHoldsForSections_powersSections_of_stepC_modP
#audit_axioms lemmaTwoHoldsAtPowers_of_glue
#audit_axioms exists_isSimpleRing_separable_hasK1InjPowerWitness_of_glue
