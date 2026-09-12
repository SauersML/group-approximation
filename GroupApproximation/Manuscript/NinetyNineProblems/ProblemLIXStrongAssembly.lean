import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIXStrong
import GroupApproximation.CharClass.LIXKGenSection
import GroupApproximation.CharClass.LemmaTwoOfHsqHresHclass
import GroupApproximation.Meta.AxiomGuard

/-!
# STW Problem LIX, strengthened: the endpoint assembly over the agreed section family

`ProblemLIXStrong.lean` states the stronger theorem over two named propositions the
construction still owes, `Corollary4Powers n b` and `LemmaTwoHoldsForSections n (b k)`, with
the section family `b` passed as data.  This file fixes that family to the one the lanes agreed
on and proves every arrow of the assembly that does not wait on Step C or Step D, so that the day
the two propositions are theorems the Palomar solution needs only one-line wrappers.

* `powersSections n k j := CharClass.KGen.bVecK n (k - 1)` — the section of degree `k` at every
  stage `j`.  `KGen.psiVec n (k - 1)` has degree `k` because `LIX.Powers.joinC (k - 1)` has
  degree `k`; `b 0` is never consulted, since every prime divides `0`.
* `powersSections_one` — at exponent `1` the family is the tautological section `Gen.bVec n`
  (`Ψ_0 = id`, `KGen.bVecK_zero_eq`).
* `lemmaTwoHoldsForSections_powersSections_one_iff` — so Lemma 2 for the family at exponent `1`
  is exactly the rank-`n` `LIX.Gen.LemmaTwoHolds n`, the input of the rank-`n` answer.
* `lemmaTwoHoldsForSections_powersSections_two_one` — at rank two that input is the landed
  mod-2 theorem `CharClass.lemmaTwoHolds`, so the exponent-`1` instance is a theorem today.
* `exists_isSimpleRing_separable_hasK1InjPowerWitness_of_powersSections` — the stronger theorem
  over `lix-tower`'s arrow at exactly this family and the Step C / Step D inputs at exactly this
  family, which is the form the endpoint consumes when those land.
-/

namespace GroupApproximation
namespace NinetyNineProblems

noncomputable section

/-- **The agreed section family**: at exponent `k`, the tautological point of `S^{2n+1}`
composed with the `k`-fold map of degree `k`, at every stage of the rank-`n` tower. -/
def powersSections (n : ℕ) :
    ℕ → ∀ j : ℕ, CharClass.Gen.baseM n (LIX.Gen.lixDD n j) → Fin (n + 1) → ℂ :=
  fun k j => CharClass.KGen.bVecK (dd := LIX.Gen.lixDD n j) n (k - 1)

/-- **At exponent `1` the family is the tautological section**, because the degree-one map
`Ψ_0` is the identity. -/
theorem powersSections_one (n j : ℕ) :
    powersSections n 1 j = CharClass.Gen.bVec (dd := LIX.Gen.lixDD n j) n := by
  funext m
  exact CharClass.KGen.bVecK_zero_eq n m

/-- **Lemma 2 for the family at exponent `1` is the rank-`n` Lemma 2.** -/
theorem lemmaTwoHoldsForSections_powersSections_one_iff (n : ℕ) :
    LemmaTwoHoldsForSections n (powersSections n 1) ↔ LIX.Gen.LemmaTwoHolds n :=
  forall_congr' fun j => by rw [powersSections_one]

/-- **At rank two the exponent-`1` instance is a theorem**: it is the landed mod-2 Lemma 2. -/
theorem lemmaTwoHoldsForSections_powersSections_two_one :
    LemmaTwoHoldsForSections 2 (powersSections 2 1) :=
  (lemmaTwoHoldsForSections_powersSections_one_iff 2).mpr
    (LIX.lemmaTwoHolds_iff_gen.mp CharClass.lemmaTwoHolds)

/-- **The stronger theorem over the agreed family.**  `lix-tower`'s arrow at
`powersSections n`, together with Lemma 2 at `powersSections n k` for every exponent `k` that
some prime dividing `n` misses, gives a nontrivial simple separable C⋆-algebra carrying the power
witness. -/
theorem exists_isSimpleRing_separable_hasK1InjPowerWitness_of_powersSections (n : ℕ)
    (hn : 2 ≤ n) (hcor4 : Corollary4Powers n (powersSections n))
    (h : ∀ p : ℕ, p.Prime → p ∣ n → ∀ k : ℕ, ¬ p ∣ k →
      LemmaTwoHoldsForSections n (powersSections n k)) :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleRing A ∧ TopologicalSpace.SeparableSpace A ∧
        HasK1InjPowerWitness A n :=
  exists_isSimpleRing_separable_hasK1InjPowerWitness_of_lemmaTwo_data n hn hcor4 h

/-- **The same, read as a refutation of `K₁`-injectivity at every rank.** -/
theorem exists_simple_separable_not_k1Inj_of_powersSections (n : ℕ) (hn : 2 ≤ n)
    (hcor4 : Corollary4Powers n (powersSections n))
    (h : ∀ p : ℕ, p.Prime → p ∣ n → ∀ k : ℕ, ¬ p ∣ k →
      LemmaTwoHoldsForSections n (powersSections n k)) :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleCStar A ∧ TopologicalSpace.SeparableSpace A ∧ ¬ K1Inj A :=
  exists_simple_separable_not_k1Inj_of n hn (hcor4 h)

end

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_axioms powersSections
#audit_axioms powersSections_one
#audit_axioms lemmaTwoHoldsForSections_powersSections_one_iff
#audit_axioms lemmaTwoHoldsForSections_powersSections_two_one
#audit_axioms exists_isSimpleRing_separable_hasK1InjPowerWitness_of_powersSections
#audit_axioms exists_simple_separable_not_k1Inj_of_powersSections
