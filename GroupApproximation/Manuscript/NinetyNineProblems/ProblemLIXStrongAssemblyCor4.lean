import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIXStrongAssembly
import GroupApproximation.Analysis.LIXCor4PowersDiag
import GroupApproximation.Meta.AxiomGuard

/-!
# STW Problem LIX, strengthened: Corollary 4 discharged, one named input left

`ProblemLIXStrong.lean` states the stronger theorem over `ClimbedPowersOutside n`, and
`ProblemLIXStrongAssembly.lean` over two inputs at the agreed family `powersSections`:
`lix-tower`'s arrow `Corollary4Powers n (powersSections n)` and Lemma 2 at `powersSections n k`
for the exponents a prime dividing `n` misses.

The arrow is now a theorem: `LIX.Gen.corollary4Powers n hn : Corollary4Powers n (degreeFamily n)`
(`Analysis/LIXCor4PowersDiag.lean`), and `degreeFamily n` is `powersSections n` by definition.  So
the construction owes exactly one named proposition,

    LemmaTwoHoldsAtPowers n :=
      ∀ p, p.Prime → p ∣ n → ∀ k, ¬ p ∣ k → LemmaTwoHoldsForSections n (powersSections n k),

Lemma 2 at every stage of the rank-`n` tower for the section of degree `k`, for every exponent `k`
some prime dividing `n` misses.  `climbedPowersOutside_of_lemmaTwoHoldsAtPowers` turns it into the
proposition the Palomar solution carries, and the two endpoint readings follow with no further
input.
-/

namespace GroupApproximation
namespace NinetyNineProblems

noncomputable section

/-- **The agreed family is `lix-tower`'s degree family**, definitionally. -/
theorem powersSections_eq_degreeFamily (n : ℕ) : powersSections n = LIX.Gen.degreeFamily n :=
  rfl

/-- **The one input the construction still owes**: Lemma 2 at every stage of the rank-`n` tower,
for the section of degree `k`, at every exponent `k` that some prime dividing `n` misses.

Owners: `lix-oddside` / `lix-oddside-n` for Step C with `k` zeros and `lix-evenside` /
`lix-evenside-n` for Step D mod `p`, glued by `CharClass/LIXLemmaTwoGenGlue.lean`. -/
def LemmaTwoHoldsAtPowers (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → ∀ k : ℕ, ¬ p ∣ k →
    LemmaTwoHoldsForSections n (powersSections n k)

/-- The same proposition in the per-stage form the rank-`n` glue of Lemma 2 concludes. -/
theorem lemmaTwoHoldsAtPowers_iff (n : ℕ) :
    LemmaTwoHoldsAtPowers n ↔
      ∀ p : ℕ, p.Prime → p ∣ n → ∀ k : ℕ, ¬ p ∣ k → ∀ j : ℕ,
        LIX.Gen.LemmaTwoFor n (LIX.Gen.lixDD n j) (CharClass.KGen.bVecK n (k - 1)) :=
  Iff.rfl

/-- **Corollary 4 at the agreed family**, from `lix-tower`'s theorem. -/
theorem corollary4Powers_powersSections (n : ℕ) (hn : 0 < n) :
    Corollary4Powers n (powersSections n) :=
  LIX.Gen.corollary4Powers n hn

/-- **The climbed power witness from Lemma 2 at the powers.** -/
theorem climbedPowersOutside_of_lemmaTwoHoldsAtPowers (n : ℕ) (hn : 0 < n)
    (h : LemmaTwoHoldsAtPowers n) : ClimbedPowersOutside n :=
  corollary4Powers_powersSections n hn h

/-- **The power witness at the rank-`n` limit from Lemma 2 at the powers.** -/
theorem hasK1InjPowerWitness_of_lemmaTwoHoldsAtPowers (n : ℕ) (hn : 0 < n)
    (h : LemmaTwoHoldsAtPowers n) : HasK1InjPowerWitness (LIX.Gen.LIXLimit n) n :=
  hasK1InjPowerWitness_of_climbedPowersOutside n
    (climbedPowersOutside_of_lemmaTwoHoldsAtPowers n hn h)

/-- **The stronger theorem over the one remaining input.**  For every `n ≥ 2`, Lemma 2 at the
powers gives a nontrivial simple separable C⋆-algebra carrying the power witness. -/
theorem exists_isSimpleRing_separable_hasK1InjPowerWitness_of_lemmaTwoHoldsAtPowers (n : ℕ)
    (hn : 2 ≤ n) (h : LemmaTwoHoldsAtPowers n) :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleRing A ∧ TopologicalSpace.SeparableSpace A ∧
        HasK1InjPowerWitness A n :=
  exists_isSimpleRing_separable_hasK1InjPowerWitness_of n hn
    (climbedPowersOutside_of_lemmaTwoHoldsAtPowers n (by omega) h)

/-- **The refutation of `K₁`-injectivity at every rank `n ≥ 2`**, over the same input. -/
theorem exists_simple_separable_not_k1Inj_of_lemmaTwoHoldsAtPowers (n : ℕ) (hn : 2 ≤ n)
    (h : LemmaTwoHoldsAtPowers n) :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleCStar A ∧ TopologicalSpace.SeparableSpace A ∧ ¬ K1Inj A :=
  exists_simple_separable_not_k1Inj_of n hn
    (climbedPowersOutside_of_lemmaTwoHoldsAtPowers n (by omega) h)

end

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_axioms powersSections_eq_degreeFamily
#audit_axioms LemmaTwoHoldsAtPowers
#audit_axioms lemmaTwoHoldsAtPowers_iff
#audit_axioms corollary4Powers_powersSections
#audit_axioms climbedPowersOutside_of_lemmaTwoHoldsAtPowers
#audit_axioms hasK1InjPowerWitness_of_lemmaTwoHoldsAtPowers
#audit_axioms exists_isSimpleRing_separable_hasK1InjPowerWitness_of_lemmaTwoHoldsAtPowers
#audit_axioms exists_simple_separable_not_k1Inj_of_lemmaTwoHoldsAtPowers
