import GroupApproximation.KOne.RefineLoopDischarge
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Ring-theoretic hypotheses for Leavitt `(TT)/T`

The matrix argument uses two logically independent facts.

* `HasSingleSandwichDivision R` says every nonzero `a` admits `xay = 1`.
  For unital purely infinite simple rings this is the standard
  Ara--Goodearl--Pardo characterization (Theorem 1.6 in their foundational
  treatment).  We name the exact algebraic property used by the proof rather
  than introducing a competing definition of pure infiniteness.
* `HasElementaryDiagonalClass R` says every `diag(u,1)` is elementary.  This
  is the unstable rank-two `K₁` input and is deliberately separate: pure
  infiniteness does not force `K₁(R)=0`.

The binary Leavitt algebra satisfies both facts internally in this library.
-/

namespace GroupApproximation

open MatrixDiagonalization

/-- Every nonzero element sandwiches to the identity.  In the established
ring literature, this is the operative characterization of a unital purely
infinite simple ring after the standard nontriviality and non-division-ring
hypotheses are imposed.  The bare predicate intentionally records only the
algebraic input used below: it also holds for division rings, and it is
vacuously true for the zero ring.  Consumers must therefore supply `Nontrivial R`
themselves and must not treat this predicate alone as a definition of pure
infiniteness.

(This sentence used to assert that every paper-facing consumer *does* assume
`Nontrivial R`.  That was a claim about the repository, and it is false:
`Manuscript/OneSidedMFRadical/SentenceOperativePureInfinitenessClosure.OperativePureInfinitenessInput`
is literally this predicate with no `Nontrivial` binder.  Nothing is unsound --
it is instantiated at `L_{𝔽₂}(1,2)`, which is nontrivial, and nontriviality
enters the simplicity chain independently through
`isSimpleGroup_of_rootDetection` -- but the guarantee was not the repository's
to give.) -/
def HasSingleSandwichDivision (R : Type*) [Ring R] : Prop :=
  ∀ a : R, a ≠ 0 → ∃ x y : R, x * a * y = 1

/-- The rank-two diagonal/unstable-`K₁` condition needed to absorb the
last diagonal block after strong-division elimination. -/
def HasElementaryDiagonalClass (R : Type*) [Ring R] : Prop :=
  ∀ u : Rˣ, diagUnit u ∈ elementaryGroup (Fin 2) R

namespace HasSingleSandwichDivision

variable {R S : Type*} [Ring R] [Ring S]

/-- The sandwich property is invariant under ring isomorphism. -/
theorem of_ringEquiv (e : R ≃+* S) (hS : HasSingleSandwichDivision S) :
    HasSingleSandwichDivision R :=
  MatrixDiagonalization.division_of_ringEquiv e hS

/-- Single-sandwich division already forces ring simplicity. -/
theorem isSimpleRing [Nontrivial R] (hdiv : HasSingleSandwichDivision R) :
    IsSimpleRing R := by
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  rw [← I.one_mem_iff]
  obtain ⟨a, ha, ha0⟩ :=
    SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI)
  obtain ⟨x, y, hxy⟩ := hdiv a ha0
  rw [← hxy]
  exact I.mul_mem_right (x * a) y (I.mul_mem_left x a ha)

end HasSingleSandwichDivision

namespace BinaryLeavitt

variable (k : Type) [Field k]

/-- The binary Leavitt algebra is single-sandwich divisible. -/
theorem hasSingleSandwichDivision :
    HasSingleSandwichDivision (BinaryLeavittAlgebra k) :=
  division k

/-- The binary Leavitt algebra has trivial elementary diagonal class. -/
theorem hasElementaryDiagonalClass :
    HasElementaryDiagonalClass (BinaryLeavittAlgebra k) := by
  intro u
  exact stableUnits_eq_top_holds k u

end BinaryLeavitt

end GroupApproximation
