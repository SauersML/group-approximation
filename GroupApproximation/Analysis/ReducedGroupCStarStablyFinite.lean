import GroupApproximation.Analysis.ReducedGroupCStarMFObstruction
import GroupApproximation.Analysis.UniversalKazhdanCStarConsequences

/-!
# Stable finiteness of the reduced group C⋆-algebra

`Analysis.UniversalKazhdanCStarConsequences` proves that every isometry in
every nonempty finite matrix amplification of the concrete reduced group
C⋆-algebra of `Analysis.ReducedGroupCStarTrace` is a unitary, using the
canonical faithful trace supplied by `Analysis.ReducedGroupCStarTraceFaithful`.
That statement is exactly stable finiteness in the operator-algebraic sense.

This module packages it under a name, `IsStablyFiniteCStarAlgebra`, so that the
MF obstruction can consume "`C⋆_r(G)` is stably finite" as a single hypothesis
about a C⋆-algebra rather than as a quantified matrix identity about one
particular algebra.  Nothing new is proved here: the content is entirely the
imported trace argument.

The `CStarAlgebra` instance on the concrete reduced algebra is the one
registered as `reducedGroupCStarCStarAlgebra` in
`Analysis.ReducedGroupCStarMFObstruction`; it is imported rather than restated.
-/

namespace GroupApproximation

open ReducedGroupCStarTrace

universe u

/-- Stable finiteness of a C⋆-algebra `A`, in the operator-algebraic sense:
every isometry in every finite matrix amplification of `A` is a unitary, i.e.
`star v * v = 1` forces `v * star v = 1` in each `CStarMatrix (Fin (k+1))
(Fin (k+1)) A`.  This is the sense of "stably finite" used in the
Blackadar–Kirchberg MF literature, where every MF algebra is stably finite.

This is deliberately *not* mathlib's `IsStablyFiniteRing` (`Mathlib/Data/
Matrix/Mul.lean`), which asks that every matrix ring `Matrix (Fin n) (Fin n) A`
be Dedekind-finite and mentions neither the star operation nor the norm.  For
C⋆-algebras the forward implication holds, by a polar-decomposition argument
that turns a one-sided ring inverse into an isometry.  That argument *is* now
formalized, in `Analysis.ReducedGroupCStarDedekindFinite`, as
`IsStablyFiniteCStarAlgebra.isStablyFiniteRing`; nothing in the present module
uses it, and the two predicates are kept separate so that the trace argument
below stands on its own. -/
def IsStablyFiniteCStarAlgebra (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ k : ℕ, ∀ v : CStarMatrix (Fin (k + 1)) (Fin (k + 1)) A,
    star v * v = 1 → v * star v = 1

/-- Stable finiteness follows from the isometry-is-unitary property for
matrix amplifications indexed by an arbitrary nonempty finite type.  The
imported trace results are stated at that generality, so this is the
adapter that specializes them to the `Fin (k + 1)` indexing fixed by
`IsStablyFiniteCStarAlgebra`. -/
theorem IsStablyFiniteCStarAlgebra.of_matrix_isometry_unitary
    {A : Type u} [CStarAlgebra A]
    (h : ∀ (n : Type) [Fintype n] [DecidableEq n], Nonempty n →
      ∀ v : CStarMatrix n n A, star v * v = 1 → v * star v = 1) :
    IsStablyFiniteCStarAlgebra A :=
  fun k v hv => h (Fin (k + 1)) ⟨0⟩ v hv

/-- The concrete reduced group C⋆-algebra of any group is stably finite.  This
is the canonical faithful trace of `Analysis.ReducedGroupCStarTraceFaithful`
read through the matrix amplification of `Analysis.FaithfulTracialMatrix`, as
assembled by `ReducedGroupCStarTrace.reduced_matrix_mul_star_eq_one_of_star_mul_eq_one`.
It holds for every group, with no approximation, amenability, or Kazhdan
hypothesis. -/
theorem reducedGroupCStar_isStablyFiniteCStarAlgebra (G : Type u) [Group G] :
    IsStablyFiniteCStarAlgebra (ReducedGroupCStar G) :=
  IsStablyFiniteCStarAlgebra.of_matrix_isometry_unitary
    fun n _ _ hn _ hv =>
      ReducedGroupCStarTrace.reduced_matrix_mul_star_eq_one_of_star_mul_eq_one
        G n hn hv

end GroupApproximation
