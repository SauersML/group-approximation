import GroupApproximation.Analysis.CalkinCompactIdeal
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

/-!
# (V2) Glimm's lemma, stated, and the positivity its proof reflects

`Analysis/VoiculescuPlan` describes **(V2)** in prose and names no `Prop` for
it — its only named statement is the (V1) one.  This module writes the
statement, checks that its hypotheses are not vacuous, and proves the one
algebraic fact the passage to the Calkin algebra rests on.

## The statement, and two choices in it

Glimm's lemma says that for a C\*-subalgebra `A ⊆ B(H)` meeting the compacts
only in `0`, every state of `A` is approximated, on any finite set and to any
tolerance, by a vector state at a vector escaping any given finite-dimensional
subspace.  Two choices are worth naming because they differ from the plan's
prose.

*The obstruction is a subspace, not a projection.*  The prose asks for
`P ξ = 0` with `P` a finite-rank projection; the statement below asks for
`ξ ∈ Vᗮ` with `V` finite-dimensional.  These are the same condition, and the
subspace form avoids carrying a projection and its idempotence through every
consumer.  (V3) recovers the projection form through
`Submodule.starProjection`, which (V1a) already uses.

*Separability is absent.*  The plan says "separable `A`", and separability is
genuinely needed — but at (V3) and (V4), for the diagonal over a dense
sequence.  The finite-set statement below does not use it, and a hypothesis
that the proof does not consume is a hypothesis the consumer has to discharge
for nothing.

## Why the hypotheses are not vacuous, and what they force

`A` contains `1`, and in finite dimensions `1` is compact, so
`A ∩ K(H) = 0` forces `H` to be infinite-dimensional as soon as it is
nonzero.  That is `not_finiteDimensional_of_compactMem_eq_zero` below, and it
is the same check that refuted `Theorem4PrintedPairStatement`: a statement
about operator algebras whose hypotheses secretly pin `H` to a finite
dimension is a statement about nothing.

## The positivity reflection, and the theorem it avoids

The passage from a state of `A` to a state of `B(H)` annihilating `K(H)` runs
through the Calkin algebra, and needs that a positive element of the image
comes from a positive element of `A`.  The usual route is "an injective
⋆-homomorphism of C\*-algebras is isometric", which is in neither Mathlib at
the pinned revision nor this tree, and is a module in its own right.

It is avoidable.  If `a` is self-adjoint and its negative part is compact,
then that negative part lies in `A` — the continuous calculus does not leave a
closed subalgebra — so it lies in `A ∩ K(H) = 0` and vanishes, and `a = a⁺` is
positive.  Stated that way the lemma mentions no order on the Calkin algebra
at all, which matters here: `Q(H)` is a general C\*-algebra and carries no
registered order, so a hypothesis `0 ≤ π a` would drag the local
`spectralOrder` instances into every consumer.  `B(H)` itself needs no such
care — `ContinuousLinearMap.instLoewnerPartialOrder` and
`ContinuousLinearMap.instStarOrderedRing` are registered.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace
open scoped ComplexOrder

noncomputable section

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The statement -/

/-- **(V2) Glimm's lemma.**  For a closed `⋆`-subalgebra of `B(H)` meeting the
compacts only in `0`, every state is approximated on any finite set by a vector
state at a unit vector orthogonal to any given finite-dimensional subspace. -/
def GlimmLemmaStatement : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : StarSubalgebra ℂ (H →L[ℂ] H)), IsClosed (A : Set (H →L[ℂ] H)) →
      (∀ T ∈ A, IsCompactOperator T → T = 0) →
      ∀ φ : ↥A →ₚ[ℂ] ℂ, φ 1 = 1 →
        ∀ (F : Finset ↥A) (ε : ℝ), 0 < ε →
          ∀ V : Submodule ℂ H, FiniteDimensional ℂ V →
            ∃ ξ : H, ‖ξ‖ = 1 ∧ ξ ∈ Vᗮ ∧
              ∀ a ∈ F, ‖⟪ξ, (a : H →L[ℂ] H) ξ⟫_ℂ - φ a‖ < ε

/-! ## The hypotheses force an infinite-dimensional space -/

/-- **The model test.**  A subalgebra meeting the compacts only in `0` can live
only on an infinite-dimensional space: it contains `1`, and in finite dimensions
the identity is compact.  So the statement above is not secretly a statement
about finite matrices, which is exactly how the printed pair binder of
`Analysis/ShulmanFillNormingPrintedPairRefuted` failed. -/
theorem not_finiteDimensional_of_compactMem_eq_zero [Nontrivial H]
    (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (hAK : ∀ T ∈ A, IsCompactOperator T → T = 0) :
    ¬ FiniteDimensional ℂ H := by
  intro hfin
  haveI : ProperSpace H := FiniteDimensional.proper ℂ H
  have hcpt : IsCompactOperator ((1 : H →L[ℂ] H) : H → H) :=
    isCompactOperator_id_iff_locallyCompactSpace.mpr inferInstance
  have hone : (1 : H →L[ℂ] H) = 0 := hAK 1 A.one_mem hcpt
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  refine hx ?_
  have h := congrArg (fun T : H →L[ℂ] H ↦ T x) hone
  calc x = (1 : H →L[ℂ] H) x := rfl
    _ = (0 : H →L[ℂ] H) x := h
    _ = 0 := rfl

/-! ## The positivity reflection -/

/-- **The reflection.**  A self-adjoint element of `A` whose negative part is
compact is positive.  This is what the Calkin passage needs, in the one form
that mentions no order on the quotient: the hypothesis `0 ≤ π a` is turned into
compactness of `a⁻` by the naturality of the continuous calculus, and here the
subalgebra swallows it. -/
theorem nonneg_of_negPart_isCompactOperator
    {A : StarSubalgebra ℂ (H →L[ℂ] H)} (hA : IsClosed (A : Set (H →L[ℂ] H)))
    (hAK : ∀ T ∈ A, IsCompactOperator T → T = 0)
    {a : H →L[ℂ] H} (haA : a ∈ A) (hsa : IsSelfAdjoint a)
    (hcpt : IsCompactOperator (a⁻ : H →L[ℂ] H)) : 0 ≤ a := by
  haveI : IsClosed (A : Set (H →L[ℂ] H)) := hA
  have hmem : (a⁻ : H →L[ℂ] H) ∈ A := by
    rw [CFC.negPart_def]
    exact cfcₙ_mem _ haA
  have hzero : (a⁻ : H →L[ℂ] H) = 0 := hAK _ hmem hcpt
  have hps : (a⁺ : H →L[ℂ] H) = a := by
    have h := CFC.posPart_sub_negPart a hsa
    rwa [hzero, sub_zero] at h
  exact (CFC.posPart_eq_self a).mp hps

end

end ShulmanFill
end GroupApproximation
