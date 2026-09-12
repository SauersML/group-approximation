import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIXStrongAssemblyTwoLocal
import GroupApproximation.CharClass.LIXStepDGenWuData
import GroupApproximation.Meta.AxiomGuard

/-!
# STW Problem LIX, strengthened: the prime `2` closed, and the ranks `2 ^ m` unconditional

`ProblemLIXStrongAssemblyTwo` names two inputs at the prime `2`.  `ProblemLIXStrongAssemblyTwoLocal`
proves the local data.  This file proves the mod-`2` Wu data at every rank `n ≠ 0`: the witnesses are
the geometric base `baseY (lixDD n j)`, the spheres `S¹` and `S^{2n+1}`, the Künneth projections
`CharClass.KnLix.prY`, `prS1`, `prSodd`, the sphere top classes, and `CharClass.Gen.nonempty_wuStepDData_lixN`
at every stage and corner unitary.

At the ranks `n = 2 ^ m` the prime `2` is the only prime dividing `n`, so `LemmaTwoHoldsAtPowers (2 ^ m)`
is a theorem, and with it the stronger theorem at those ranks: a nontrivial simple separable C⋆-algebra
with a unitary whose stabilisation is null-homotopic and whose powers leave `U₀` at every odd exponent.
-/

namespace GroupApproximation
namespace NinetyNineProblems

noncomputable section

/-- **The mod-`2` Wu data at every stage, at every rank `n ≠ 0`.** -/
theorem lemmaTwoPowersTwoWuData_holds (n : ℕ) [NeZero n] : LemmaTwoPowersTwoWuData n :=
  ⟨fun j => TopCat.of (CharClass.baseY (LIX.Gen.lixDD n j)),
    fun _ => TopCat.of (ThirdParty.HamSandwich.SphereOddDegree.Sphere 1),
    fun _ => TopCat.of (ThirdParty.HamSandwich.SphereOddDegree.Sphere (2 * n + 1)),
    fun j => CharClass.KnLix.prY n (LIX.Gen.lixDD n j),
    fun j => CharClass.KnLix.prS1 n (LIX.Gen.lixDD n j),
    fun j => CharClass.KnLix.prSodd n (LIX.Gen.lixDD n j),
    fun _ => CharClass.hasSphereCohomology_sphere 1 le_rfl,
    fun _ => CharClass.hasSphereCohomology_sphere (2 * n + 1) (by omega),
    fun _ => CharClass.sphereTopClass 1 le_rfl,
    fun _ => CharClass.sphereTopClass (2 * n + 1) (by omega),
    fun j G hGc hGu => CharClass.Gen.nonempty_wuStepDData_lixN n j G hGc hGu⟩

/-- **`LemmaTwoHoldsAtPowers` at the ranks `2 ^ m`, unconditionally.** -/
theorem lemmaTwoHoldsAtPowers_two_pow_holds (m : ℕ) (hm : 1 ≤ m) :
    LemmaTwoHoldsAtPowers (2 ^ m) := by
  haveI : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
  exact lemmaTwoHoldsAtPowers_two_pow_of_wuData m hm (lemmaTwoPowersTwoWuData_holds (2 ^ m))

/-- **The stronger theorem at the ranks `2 ^ m`, unconditionally**: a nontrivial simple separable
C⋆-algebra carrying the power witness at rank `2 ^ m`. -/
theorem exists_isSimpleRing_separable_hasK1InjPowerWitness_two_pow (m : ℕ) (hm : 1 ≤ m) :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleRing A ∧ TopologicalSpace.SeparableSpace A ∧
        HasK1InjPowerWitness A (2 ^ m) := by
  have h2le : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  exact exists_isSimpleRing_separable_hasK1InjPowerWitness_of_lemmaTwoHoldsAtPowers (2 ^ m) h2le
    (lemmaTwoHoldsAtPowers_two_pow_holds m hm)

end

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_axioms lemmaTwoPowersTwoWuData_holds
#audit_axioms lemmaTwoHoldsAtPowers_two_pow_holds
#audit_axioms exists_isSimpleRing_separable_hasK1InjPowerWitness_two_pow
