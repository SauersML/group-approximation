import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.Data.Set.Finite.Basic

/-!
# Finite presentations of noncommutative algebras

Mathlib's existing finite-presentation API is phrased using multivariate
polynomials and therefore applies to commutative algebras.  The coefficient
rings in this project are noncommutative.  This file records the corresponding
universal-algebra notion using a free associative algebra and a finite set of
equations.

The relation itself is allowed to be Prop-valued, matching `RingQuot`; the
finiteness condition is imposed on the set of pairs for which it holds.
-/

namespace GroupApproximation.Algebra

universe u v

/-- A noncommutative `k`-algebra is finitely presented if it is the quotient
of a free associative `k`-algebra on finitely many generators by finitely many
equations. -/
class IsFinitelyPresentedNC (k : Type u) (A : Type v)
    [CommSemiring k] [Semiring A] [Algebra k A] : Prop where
  out : ∃ (n : ℕ) (r : FreeAlgebra k (Fin n) → FreeAlgebra k (Fin n) → Prop),
    Set.Finite {p : FreeAlgebra k (Fin n) × FreeAlgebra k (Fin n) | r p.1 p.2} ∧
      Nonempty (A ≃ₐ[k] RingQuot r)

end GroupApproximation.Algebra

namespace GroupApproximation.Ring

universe u

/-- An associative unital ring is finitely presented if it is a quotient of
the free associative ring on finitely many generators by finitely many
equations.  The free associative ring is expressed as a free `ℤ`-algebra so
that characteristic relations, such as `2 = 0`, are part of the presentation
rather than being hidden in a coefficient ring. -/
class IsFinitelyPresentedNC (A : Type u) [Ring A] : Prop where
  out : ∃ (n : ℕ)
      (r : FreeAlgebra ℤ (Fin n) → FreeAlgebra ℤ (Fin n) → Prop),
    Set.Finite
        {p : FreeAlgebra ℤ (Fin n) × FreeAlgebra ℤ (Fin n) | r p.1 p.2} ∧
      Nonempty (A ≃+* RingQuot r)

end GroupApproximation.Ring
