import GroupApproximation.AlgTop.BundleCalculusProjection
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.ContinuousMap.ContinuousSqrt

/-!
# Bundle calculus II: ordering the section algebra, and transport

Two things, both in service of letting the rest of the campaign keep the model
it already has.

## The section algebra is a `StarOrderedRing`

The campaign's ambient algebra is `SectionAlgebra X ι = C(X, CStarMatrix ι ι ℂ)`
(`Analysis/LIXCornerAlgebra.lean`): continuous matrix-valued functions.  That
type is a `CStarAlgebra` and carries the pointwise `PartialOrder`, but at the
Mathlib pin it has **no `StarOrderedRing` instance**, and without one there is no
continuous functional calculus over `ℝ≥0`, hence no inverse square root, hence no
route to `unitaryConj_of_norm_sub_lt_one`.  The gap is a single missing instance:
`ContinuousMap.instStarOrderedRing` derives `StarOrderedRing C(α, R)` from
`ContinuousSqrt R`, and Mathlib instantiates `ContinuousSqrt` only for `ℝ`, `ℝ≥0`
and `ℂ`.

The instance is available for *every* ordered C*-algebra, and this file supplies
it.  `ContinuousSqrt` asks for a continuous choice of `s` with `b = a + s * s` on
the set where `a ≤ b`; take `s = CFC.sqrt (b - a)`, whose continuity on the
positive cone is `CFC.continuousOn_sqrt`.  So `StarOrderedRing C(X, A)` holds for
any C*-algebra `A` with its order, `SectionAlgebra` inherits it, and the homotopy
invariance of `BundleCalculusProjection` applies to the existing model verbatim.
No lane has to change its ambient algebra.

The instance is given low priority so that Mathlib's `instContinuousSqrtRCLike`
still wins on the scalar fields, where it is the cheaper one.

## Transport

Every operation on bundles that must be well defined on isomorphism classes --
pullback along a map of base spaces, restriction, evaluation at a point,
inclusion of a corner -- is a star homomorphism of the ambient algebra.  So
prove well definedness once, for homomorphisms.  `MurrayVonNeumannEquiv.map`
(`KTheory/MatrixProjection.lean`) already does this for bundle isomorphism; the
missing half is unitary conjugacy, where unitality of the homomorphism is
exactly what makes the image of a unitary a unitary.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace BundleCalculus

section Transport

variable {R S F : Type*}

/-- A unital star homomorphism carries unitary conjugacy forward.  Unitality is
doing the work: the image of a unitary is a unitary only because `1` goes to
`1`.  The `MurrayVonNeumannEquiv` counterpart is `MurrayVonNeumannEquiv.map`. -/
theorem UnitaryConj.map [Monoid R] [StarMul R] [Monoid S] [StarMul S] [FunLike F R S]
    [MonoidHomClass F R S] [StarHomClass F R S] {p q : R} (f : F) (h : UnitaryConj p q) :
    UnitaryConj (f p) (f q) := by
  obtain ⟨u, hu, huq⟩ := h
  refine ⟨f u, Unitary.mem_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · rw [← map_star, ← map_mul, Unitary.star_mul_self_of_mem hu, map_one]
  · rw [← map_star, ← map_mul, Unitary.mul_star_self_of_mem hu, map_one]
  · rw [← map_star, ← map_mul, ← map_mul, huq]

end Transport

section ContinuousSqrt

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Every ordered C*-algebra has a continuous square root of differences.**
`ContinuousSqrt` wants a continuous `s` with `b = a + s * s` wherever `a ≤ b`,
and `CFC.sqrt (b - a)` is one: it is nonnegative, it squares to `b - a`, and
`CFC.continuousOn_sqrt` gives its continuity on the positive cone.

The point of the instance is `ContinuousMap.instStarOrderedRing`, which turns it
into `StarOrderedRing C(X, A)` -- the instance the campaign's section algebra was
missing.  Low priority, so `instContinuousSqrtRCLike` keeps precedence on `ℝ`,
`ℝ≥0` and `ℂ`. -/
noncomputable instance (priority := 50) instContinuousSqrtOfCStarAlgebra :
    ContinuousSqrt A where
  sqrt x := CFC.sqrt (x.2 - x.1)
  continuousOn_sqrt := by
    have hsub : ContinuousOn (fun x : A × A => x.2 - x.1) {x : A × A | x.1 ≤ x.2} :=
      (continuous_snd.sub continuous_fst).continuousOn
    have hmaps : Set.MapsTo (fun x : A × A => x.2 - x.1)
        {x : A × A | x.1 ≤ x.2} {a : A | 0 ≤ a} := fun x hx => sub_nonneg.mpr hx
    exact CFC.continuousOn_sqrt.comp' hsub hmaps
  sqrt_nonneg _ _ := CFC.sqrt_nonneg _
  sqrt_mul_sqrt x hx := by
    rw [CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hx)]
    abel

end ContinuousSqrt

section SectionAlgebra

open scoped ComplexOrder

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The instance ladder of the campaign's section algebra, compile-checked.
The third of these is what `instContinuousSqrtOfCStarAlgebra` above supplies and
what the pin does not. -/
example : CStarAlgebra C(X, CStarMatrix ι ι ℂ) := inferInstance

example : PartialOrder C(X, CStarMatrix ι ι ℂ) := inferInstance

example : StarOrderedRing C(X, CStarMatrix ι ι ℂ) := inferInstance

/-- **Homotopy invariance in the campaign's section algebra.**  A continuous path
of projection-valued matrix functions over `X` has unitarily conjugate ends, so
isomorphic ends.  This is `unitaryConj_of_path` with the instance ladder above
discharged, and its elaboration is the compile-time proof that the ladder
resolves. -/
theorem unitaryConj_of_path_sectionAlgebra {P : ℝ → C(X, CStarMatrix ι ι ℂ)}
    (hP : Continuous P) (hproj : ∀ t : ℝ, IsStarProjection (P t)) :
    UnitaryConj (P 0) (P 1) :=
  unitaryConj_of_path hP hproj

theorem murrayVonNeumannEquiv_of_path_sectionAlgebra {P : ℝ → C(X, CStarMatrix ι ι ℂ)}
    (hP : Continuous P) (hproj : ∀ t : ℝ, IsStarProjection (P t)) :
    MurrayVonNeumannEquiv (P 0) (P 1) :=
  murrayVonNeumannEquiv_of_path hP hproj

/-- The form the consumers want: the index space is a parameter, so
`s := Set.Icc 0 1` is homotopy invariance and `s := Set.univ` over a connected
`Y` is constancy of the isomorphism class along `Y`. -/
theorem unitaryConj_of_isPreconnected_sectionAlgebra {Y : Type*} [TopologicalSpace Y]
    {s : Set Y} (hs : IsPreconnected s) {P : Y → C(X, CStarMatrix ι ι ℂ)}
    (hP : Continuous P) (hproj : ∀ y, IsStarProjection (P y))
    {y₀ y₁ : Y} (h₀ : y₀ ∈ s) (h₁ : y₁ ∈ s) :
    UnitaryConj (P y₀) (P y₁) :=
  unitaryConj_of_isPreconnected hs hP hproj h₀ h₁

end SectionAlgebra

end BundleCalculus
end GroupApproximation
