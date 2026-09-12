import GroupApproximation.Analysis.LIXStablyFinite
import GroupApproximation.Analysis.ReducedGroupCStarStablyFinite
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIXStrong
import GroupApproximation.Meta.AxiomGuard

/-!
# STW Problem LIX, strengthened: the counterexample algebra is stably finite

The unital simple C⋆-algebras that are not `K₁`-injective must be finite in a strong sense for the
question to have content: properly infinite algebras are `K₁`-injective.  This file records that
the LIX counterexample algebra is **stably finite** at every rank, so the strengthened theorem of
`ProblemLIXStrong.lean` can carry stable finiteness as one more conjunct.

## The rendering

`IsStablyFiniteMatrices A` says that every isometry of every matrix amplification of `A` is a
unitary, with the size a natural number `m`, never `k + 1`: a `Fin (k + 1)` in a Comparator
statement can have its `Fintype` instance captured by a different instance in the solution
environment (the `SimplexCategory` trap recorded in the Palomar LIX memory), while an fvar `m`
cannot.  The size `m = 0` costs nothing, since `M₀(A)` is the zero ring.  It mentions only Mathlib
names (`CStarMatrix`, `star`, `*`, `1`), needs no order instance, and agrees with the repository's
`IsStablyFiniteCStarAlgebra` (`isStablyFiniteMatrices_iff`).  It is the body of the inline
stable-finiteness conjunct of `Palomar/LIXStrongChallenge.lean`.
-/

namespace GroupApproximation
namespace NinetyNineProblems

universe u

/-- **Stable finiteness, in Mathlib vocabulary alone**: every isometry in every matrix
amplification of `A` is a unitary. -/
def IsStablyFiniteMatrices (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (m : ℕ) (x : CStarMatrix (Fin m) (Fin m) A), star x * x = 1 → x * star x = 1

/-- `M₀(A)` is the zero ring, so the size-zero clause holds for want of an entry. -/
theorem cstarMatrix_fin_zero_eq {A : Type u} [CStarAlgebra A]
    (x y : CStarMatrix (Fin 0) (Fin 0) A) : x = y :=
  CStarMatrix.ext fun i _ => i.elim0

/-- The Mathlib-only rendering agrees with the repository's predicate. -/
theorem isStablyFiniteMatrices_iff (A : Type u) [CStarAlgebra A] :
    IsStablyFiniteMatrices A ↔ IsStablyFiniteCStarAlgebra A := by
  constructor
  · intro h k v hv
    exact h (k + 1) v hv
  · intro h m v hv
    rcases m with _ | k
    · exact cstarMatrix_fin_zero_eq _ _
    · exact h k v hv

/-- **The rank-`n` counterexample algebra is stably finite**, for every `n ≠ 0`. -/
theorem lixLimit_isStablyFiniteMatrices (n : ℕ) [NeZero n] :
    IsStablyFiniteMatrices (LIX.Gen.LIXLimit n) := by
  intro m v hv
  rcases m with _ | k
  · exact cstarMatrix_fin_zero_eq _ _
  · exact LIX.Gen.lixLimit_mul_star_eq_one_of_star_mul_eq_one n (Fin (k + 1)) ⟨0⟩ hv

/-- The same in the repository's vocabulary. -/
theorem lixLimit_isStablyFiniteCStarAlgebra (n : ℕ) [NeZero n] :
    IsStablyFiniteCStarAlgebra (LIX.Gen.LIXLimit n) :=
  (isStablyFiniteMatrices_iff _).mp (lixLimit_isStablyFiniteMatrices n)

/-- **Stable finiteness at the ranks of the strengthened theorem** (`2 ≤ n`). -/
theorem lixLimit_stablyFinite (n : ℕ) (hn : 2 ≤ n) :
    IsStablyFiniteMatrices (LIX.Gen.LIXLimit n) := by
  haveI : NeZero n := ⟨by omega⟩
  exact lixLimit_isStablyFiniteMatrices n

/-- The rank-two algebra of the printed answer `ProblemLIX.lean` is stably finite. -/
theorem lixLimit_two_isStablyFiniteMatrices : IsStablyFiniteMatrices LIX.LIXLimit :=
  lixLimit_isStablyFiniteMatrices 2

/-- **The strengthened theorem with stable finiteness**, over the same named input as
`exists_isSimpleRing_separable_hasK1InjPowerWitness_of`: for every `n ≥ 2` the counterexample
algebra is nontrivial, simple, separable, stably finite, and carries the power witness. -/
theorem exists_isSimpleRing_separable_stablyFinite_hasK1InjPowerWitness_of (n : ℕ) (hn : 2 ≤ n)
    (h : ClimbedPowersOutside n) :
    ∃ (A : Type) (_ : CStarAlgebra A),
      Nontrivial A ∧ IsSimpleRing A ∧ TopologicalSpace.SeparableSpace A ∧
        IsStablyFiniteMatrices A ∧ HasK1InjPowerWitness A n := by
  haveI : NeZero n := ⟨by omega⟩
  refine ⟨LIX.Gen.LIXLimit n, inferInstance, inferInstance, ?_,
    LIX.Gen.lixLimit_separableSpace n, lixLimit_isStablyFiniteMatrices n,
    hasK1InjPowerWitness_of_climbedPowersOutside n h⟩
  exact (isSimpleCStar_iff_isSimpleRing (LIX.Gen.LIXLimit n)).mp
    (LIX.Gen.lixLimit_isSimpleCStar n)

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_axioms IsStablyFiniteMatrices
#audit_axioms isStablyFiniteMatrices_iff
#audit_axioms lixLimit_isStablyFiniteMatrices
#audit_axioms lixLimit_isStablyFiniteCStarAlgebra
#audit_axioms lixLimit_stablyFinite
#audit_axioms lixLimit_two_isStablyFiniteMatrices
#audit_axioms exists_isSimpleRing_separable_stablyFinite_hasK1InjPowerWitness_of
