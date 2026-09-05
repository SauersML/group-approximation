import GroupApproximation.AlgTop.BundleCalculusProjection
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.ContinuousMap.ContinuousSqrt

/-!
# Bundle calculus II: transport along star homomorphisms, and the matrix model

Two things the consuming lanes need immediately, and which are cheap once
`BundleCalculusProjection` is in hand.

**Transport.**  Every operation on bundles that is going to be well defined on
isomorphism classes -- pullback along a map of base spaces, restriction to a
subspace, evaluation at a point, inclusion of a corner -- is a homomorphism of
the ambient algebra that respects `star`.  So rather than proving well
definedness once per operation, prove it once for homomorphisms:

    MvNEquiv p q  →  MvNEquiv (f p) (f q)

for any `f` in a `MulHomClass` that is also a `StarHomClass`, and the same for
unitary conjugacy with `MonoidHomClass`.  Mathlib's `IsStarProjection.map`
already says a homomorphic image of a projection is a projection, so a
consumer's pullback lemma is two lines, not two pages.

**The matrix model.**  `BundleAlg X N` fixes the ambient algebra for the whole
campaign as

    CStarMatrix (Fin N) (Fin N) C(X, ℂ)

-- matrices with entries in the functions, *not* functions valued in matrices.
The reason is instance availability rather than taste.  `Matrix` carries no
C*-norm at all, and `C(X, A)` becomes a `StarOrderedRing` only through
`ContinuousMap.instStarOrderedRing`, which wants `ContinuousSqrt A`; that class
exists for `ℝ`, `ℝ≥0` and `ℂ` and for nothing else.  So `C(X, CStarMatrix n n ℂ)`
has no order, hence no continuous functional calculus, hence no route to
homotopy invariance.  Turning the expression inside out fixes all three: `C(X,ℂ)`
is ordered because `ℂ` is, and `CStarMatrix.instStarOrderedRing` then carries the
order up to the matrices.

Callers must `open scoped ComplexOrder`.  Without it the missing `PartialOrder ℂ`
surfaces much later as a missing `StarOrderedRing`, which is a confusing place to
start debugging.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace BundleCalculus

section Transport

variable {R S F : Type*}

/-- A star homomorphism carries Murray-von Neumann equivalence forward: the
partial isometry is the image of the partial isometry. -/
theorem MvNEquiv.map [Mul R] [Star R] [Mul S] [Star S] [FunLike F R S]
    [MulHomClass F R S] [StarHomClass F R S] {p q : R} (f : F) (h : MvNEquiv p q) :
    MvNEquiv (f p) (f q) := by
  obtain ⟨v, h₁, h₂⟩ := h
  exact ⟨f v, by rw [← map_star, ← map_mul, h₁], by rw [← map_star, ← map_mul, h₂]⟩

/-- A unital star homomorphism carries unitary conjugacy forward.  Unitality is
what is doing the work: the image of a unitary is a unitary only because `1` goes
to `1`. -/
theorem UnitaryConj.map [Monoid R] [StarMul R] [Monoid S] [StarMul S] [FunLike F R S]
    [MonoidHomClass F R S] [StarHomClass F R S] {p q : R} (f : F) (h : UnitaryConj p q) :
    UnitaryConj (f p) (f q) := by
  obtain ⟨u, hu, huq⟩ := h
  refine ⟨f u, Unitary.mem_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [← map_star, ← map_mul, Unitary.star_mul_self_of_mem hu, map_one]
  · rw [← map_star, ← map_mul, Unitary.mul_star_self_of_mem hu, map_one]
  · rw [← map_star, ← map_mul, ← map_mul, huq]

end Transport

section Complement

variable {R : Type*} [Ring R] [StarRing R] {p : R}

/-- The complementary projection.  This is Mathlib's `IsStarProjection.one_sub`,
named here because in the projection model it is the complement of a subbundle
inside the trivial bundle of rank `N`. -/
theorem isStarProjection_complement (hp : IsStarProjection p) : IsStarProjection (1 - p) :=
  hp.one_sub

theorem add_complement (p : R) : p + (1 - p) = 1 := by abel

theorem mul_complement (hp : IsStarProjection p) : p * (1 - p) = 0 := by
  have hp2 : p * p = p := hp.isIdempotentElem
  rw [mul_sub, mul_one, hp2, sub_self]

theorem complement_mul (hp : IsStarProjection p) : (1 - p) * p = 0 := by
  have hp2 : p * p = p := hp.isIdempotentElem
  rw [sub_mul, one_mul, hp2, sub_self]

end Complement

section MatrixModel

open scoped ComplexOrder

/-- The ambient algebra of the projection model: a complex vector bundle of rank
at most `N` over a compact `X` is a star projection in `BundleAlg X N`, and two
bundles are isomorphic when the projections are `MvNEquiv`. -/
abbrev BundleAlg (X : Type*) [TopologicalSpace X] [CompactSpace X] (N : ℕ) :=
  CStarMatrix (Fin N) (Fin N) C(X, ℂ)

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] {N : ℕ}

example : CStarAlgebra (BundleAlg X N) := inferInstance
example : PartialOrder (BundleAlg X N) := inferInstance
example : StarOrderedRing (BundleAlg X N) := inferInstance

/-- **Homotopy invariance in the matrix model.**  A continuous path of bundles
over `X` has isomorphic ends.  This is `unitaryConj_of_path` with the instance
ladder of `BundleAlg` discharged, and its elaboration is the compile-time check
that the ladder resolves. -/
theorem unitaryConj_of_path_bundleAlg {P : ℝ → BundleAlg X N} (hP : Continuous P)
    (hproj : ∀ t : ℝ, IsStarProjection (P t)) :
    UnitaryConj (P 0) (P 1) :=
  unitaryConj_of_path hP hproj

theorem mvNEquiv_of_path_bundleAlg {P : ℝ → BundleAlg X N} (hP : Continuous P)
    (hproj : ∀ t : ℝ, IsStarProjection (P t)) :
    MvNEquiv (P 0) (P 1) :=
  mvNEquiv_of_path hP hproj

/-- The form the consumers actually want: the index space is a parameter, so
`s := Set.Icc 0 1` is homotopy invariance and `s := Set.univ` over a connected
`X` is constancy of the isomorphism class. -/
theorem unitaryConj_of_isPreconnected_bundleAlg {Y : Type*} [TopologicalSpace Y]
    {s : Set Y} (hs : IsPreconnected s) {P : Y → BundleAlg X N} (hP : Continuous P)
    (hproj : ∀ y, IsStarProjection (P y)) {y₀ y₁ : Y} (h₀ : y₀ ∈ s) (h₁ : y₁ ∈ s) :
    UnitaryConj (P y₀) (P y₁) :=
  unitaryConj_of_isPreconnected hs hP hproj h₀ h₁

end MatrixModel

end BundleCalculus
end GroupApproximation
