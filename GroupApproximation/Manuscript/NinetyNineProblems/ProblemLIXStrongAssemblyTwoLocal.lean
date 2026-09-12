import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIXStrongAssemblyOddP
import GroupApproximation.CharClass.LIXKGenLocalNonzero
import GroupApproximation.Meta.AxiomGuard

/-!
# STW Problem LIX, strengthened: the local data at the prime `2` is a theorem

`ProblemLIXStrongAssemblyTwo` names two inputs at the prime `2`.  The first,
`LemmaTwoPowersTwoLocalData n`, is proved here for every rank: at each zero of the degree-`k`
section, the section pullback of the Thom class restricts to a nonzero local class
(`CharClass.KGen.kZeroLocalData_powers`, through the local square at every zero).

So `LemmaTwoHoldsAtPowers n` at a rank `n ≥ 2` needs exactly the mod-`2` Wu data when `2 ∣ n` and
the mod-`p` data at every odd prime dividing `n`.
-/

namespace GroupApproximation
namespace NinetyNineProblems

noncomputable section

/-- **The local data of Step C at the prime `2`, at every rank.** -/
theorem lemmaTwoPowersTwoLocalData_holds (n : ℕ) : LemmaTwoPowersTwoLocalData n :=
  CharClass.KGen.kZeroLocalData_powers n

/-- **`LemmaTwoHoldsAtPowers n` from the Wu data at the prime `2` and the mod-`p` data at the odd
primes**, the local data at the prime `2` being a theorem. -/
theorem lemmaTwoHoldsAtPowers_of_wuData_of_modPData (n : ℕ) (hn2 : 2 ≤ n)
    (hwu : 2 ∣ n → LemmaTwoPowersTwoWuData n)
    (hodd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ∣ n → LemmaTwoPowersModPData n p) :
    LemmaTwoHoldsAtPowers n :=
  lemmaTwoHoldsAtPowers_of_twoData_of_modPData n hn2
    (fun h2 => ⟨lemmaTwoPowersTwoLocalData_holds n, hwu h2⟩) hodd

/-- **At the ranks `2 ^ m` only the Wu data remains.** -/
theorem lemmaTwoHoldsAtPowers_two_pow_of_wuData (m : ℕ) (hm : 1 ≤ m)
    (hwu : LemmaTwoPowersTwoWuData (2 ^ m)) : LemmaTwoHoldsAtPowers (2 ^ m) :=
  lemmaTwoHoldsAtPowers_two_pow m hm (lemmaTwoPowersTwoLocalData_holds (2 ^ m)) hwu

end

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_axioms lemmaTwoPowersTwoLocalData_holds
#audit_axioms lemmaTwoHoldsAtPowers_of_wuData_of_modPData
#audit_axioms lemmaTwoHoldsAtPowers_two_pow_of_wuData
