import NonsoficGroupsExist.Algebra.NoncommutativeFinitePresentation
import NonsoficGroupsExist.Leavitt.UniversalLeavittOver

/-!
# The finite presentation of the binary Leavitt algebra

This file packages the defining presentation of `L_k(1,2)` as four
noncommuting generators and exactly five equations.  In particular it gives
the noncommutative finite-presentation certificate needed by the
Krstić--McCool finite-presentation theorem for Steinberg groups.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

variable (k : Type*) [Field k]

/-- The graph of the five-equation relation defining the binary Leavitt
algebra is a finite set of pairs of free-algebra elements. -/
theorem relationPairs_finite :
    Set.Finite {p : Free k × Free k | Relation k p.1 p.2} := by
  classical
  let q00 : Free k × Free k :=
    (FreeAlgebra.ι k t0 * FreeAlgebra.ι k s0, 1)
  let q01 : Free k × Free k :=
    (FreeAlgebra.ι k t0 * FreeAlgebra.ι k s1, 0)
  let q10 : Free k × Free k :=
    (FreeAlgebra.ι k t1 * FreeAlgebra.ι k s0, 0)
  let q11 : Free k × Free k :=
    (FreeAlgebra.ι k t1 * FreeAlgebra.ι k s1, 1)
  let qsum : Free k × Free k :=
    (FreeAlgebra.ι k s0 * FreeAlgebra.ι k t0 +
      FreeAlgebra.ι k s1 * FreeAlgebra.ι k t1, 1)
  let equations : Finset (Free k × Free k) :=
    {q00, q01, q10, q11, qsum}
  apply equations.finite_toSet.subset
  rintro ⟨x, y⟩ h
  change Relation k x y at h
  cases h <;> simp [equations, q00, q01, q10, q11, qsum]

/-- `L_k(1,2)` is finitely presented as a noncommutative `k`-algebra: it
has the four named generators and the five Leavitt equations. -/
instance : Algebra.IsFinitelyPresentedNC k (BinaryLeavittAlgebra k) where
  out := ⟨4, Relation k, relationPairs_finite k, ⟨AlgEquiv.refl⟩⟩

end BinaryLeavitt
end NonsoficGroupsExist
