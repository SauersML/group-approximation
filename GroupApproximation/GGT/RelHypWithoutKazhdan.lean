import GroupApproximation.Manuscript.NonMF.FournierFacioInput
import GroupApproximation.Algebra.HyperbolicInteger
import GroupApproximation.Algebra.ProductFinitePresentation

/-!
# The property (T) hypothesis of the Fournier-Facio quotient is load-bearing

`FournierFacioQuotientStatement` asks, for an infinite finitely presented
torsion-free hyperbolic group `H₀` **with property (T)** and a finitely
presented torsion-free `U`, for a finitely presented torsion-free common
target `P` that is a quotient of `H₀` and contains `U`.  Osin's small
cancellation theorem needs `H₀` non-elementary, and property (T) supplies
that: an infinite virtually cyclic group is amenable, and amenable groups with
(T) are finite.

Without (T) the statement is false, and the counterexample is entirely
in-repo: `H₀ = ℤ` is infinite, finitely presented, torsion-free and
hyperbolic (`Algebra/HyperbolicInteger`), `U = F₂` is finitely presented and
torsion-free (`FreeCommutatorWitness`), every quotient of `ℤ` is commutative,
and an injection out of `F₂` into a commutative group would make its two free
generators commute.  So the hypothesis cannot be dropped by a later editor
without this theorem objecting.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TheoremC

/-- The Fournier-Facio quotient statement with the property (T) hypothesis on
`H₀` removed. -/
def FournierFacioQuotientStatementWithoutKazhdan : Prop :=
  ∀ (H₀ U : Type) (_ : Group H₀) (_ : Group U),
    Infinite H₀ → Group.IsFinitelyPresented H₀ →
      IsPowerTorsionFree H₀ → GroupApproximation.Hyperbolic.IsHyperbolicGroup H₀ →
        Group.IsFinitelyPresented U → IsPowerTorsionFree U →
          ∃ (P : Type) (_ : Group P),
            Group.IsFinitelyPresented P ∧ IsPowerTorsionFree P ∧
              (∃ p : H₀ →* P, Function.Surjective p) ∧
              (∃ e : U →* P, Function.Injective e)

/-- **Without property (T) the quotient statement is false**: at `H₀ = ℤ` and
`U = F₂` every quotient of `H₀` is commutative, so `U` cannot embed. -/
theorem not_fournierFacioQuotientStatementWithoutKazhdan :
    ¬ FournierFacioQuotientStatementWithoutKazhdan := by
  intro h
  obtain ⟨P, instP, _, _, ⟨p, hp⟩, ⟨e, he⟩⟩ :=
    h (Multiplicative ℤ) FreeCommutatorWitness inferInstance inferInstance
      Hyperbolic.infinite_multiplicative_int inferInstance
      Hyperbolic.isPowerTorsionFree_multiplicative_int
      Hyperbolic.isHyperbolicGroup_multiplicative_int
      freeCommutatorWitness_finitelyPresented freeCommutatorWitness_torsionFree
  have hcomm : ∀ x y : P, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := hp x
    obtain ⟨b, rfl⟩ := hp y
    rw [← map_mul, ← map_mul, mul_comm]
  apply freeWitness_generators_not_commute
  apply he
  rw [map_mul, map_mul, hcomm]

end TheoremC
end NonMF
end Manuscript
end GroupApproximation
