import GroupApproximation.Analysis.ShulmanFillNormingRecognitionWiring
import GroupApproximation.Analysis.ShulmanFillNormingTailPrintedPair

/-!
# The legacy conditional recognition route

`ShulmanFill.conjugateWordNorming_of_printedPair_of_compatible'` derives
`ConjugateWordNormingStatement` from `Theorem4PrintedPairStatement`, which
`Analysis/ShulmanFillNormingPrintedPairRefuted` and
`Analysis/ShulmanFillNormingPrintedPairCharacter` refute.  This module is the
same route on `UnitalTailPairPackageStatement`, the legacy conditional package.

## What it rests on

Two Props the legacy route assumes --- `UnitalTailPairPackageStatement` and
`ShulmanSymmetricDouble.CompatibleTargetPairStatement` --- and two owed inputs
that the repair introduced and that are named rather than assumed silently:

* `ShiftedPrintedMFStatement`, MF-ness of the coordinate algebras at the printed
  models.  The unshifted route has the same input and discharges it in
  `Analysis/ShulmanFillNormingEllTwoTheorem10`; what is known about doing so
  here is in `Analysis/ShulmanFillNormingTailPrintedPair`'s docstring.
* `SeparableFaithfulInfiniteRepresentationStatement`, which is the landed
  `SeparableFaithfulRepresentationStatement` --- a theorem, proved as
  `CStarState.separableFaithfulRepresentation` --- with one clause added: the
  Hilbert space is infinite-dimensional.  The repaired binder asks for that,
  because `not_theorem4PrintedPair` shows the printed models cannot be placed
  on a finite-dimensional space at all.

The second is genuinely new work and is owed.  Two routes, either of which
suffices.  The space `CStarState.exists_typeZero_faithful_representation`
produces is the `ℓ²`-sum of `ℕ`-many GNS spaces of states on a nontrivial
algebra, each carrying a unit cyclic vector, so it is already
infinite-dimensional and the clause is a matter of proving it of that
construction.  Or, cheaper and independent of the construction: replace `H` by
`H ⊕ ℓ²(ℕ)` and `π` by `π ⊕ 0`, which stays faithful and separable and is
infinite-dimensional for free.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

universe w

section TailRecognition

variable [∀ m, Nontrivial (DoubledModel EllTwoCoefficient m)]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable [Nontrivial (H →L[ℂ] H)]
variable [Nontrivial (BlockSpace H 2 →L[ℂ] BlockSpace H 2)]
variable {C D : Type} [CStarAlgebra C] [CStarAlgebra D]
variable [TopologicalSpace.SeparableSpace D]
variable (k : C →⋆ₐ[ℂ] D) [Nonempty (CStarAmalgamRepresentation k k)]

omit [∀ (m : ℕ), Nontrivial (DoubledModel EllTwoCoefficient m)] in
/-- **Theorem 10 from the repaired package.**  `isMFAlgebra_amalgam_of_printedPair`
with the refuted binder replaced by the repaired one; the infinite-dimensionality
the repair asks of `H` is a hypothesis here and is supplied by the caller. -/
theorem isMFAlgebra_amalgam_of_tailPair
    (hT4 : UnitalTailPairPackageStatement) (hMF : ShiftedPrintedMFStatement)
    (hHinf : ¬ FiniteDimensional ℂ H) (hDmf : IsMFAlgebra D)
    (ρ₁ ρ₂ : D →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hρ₁ : Function.Injective ρ₁) (hρ₂ : Function.Injective ρ₂)
    (hρ : ρ₁.comp k = ρ₂.comp k)
    (hΛ : Function.Injective (universalCStarAmalgamEval k k
      (StarStrongAsymptoticLift.limitRep k hρ))) :
    IsMFAlgebra (UniversalCStarAmalgam k k) := by
  obtain ⟨ι, hnorm, hone, φ₁, φ₂, _hcut, hagree⟩ :=
    hT4 hHinf k hDmf ρ₁ ρ₂ hρ₁ hρ₂ hρ
  exact isMFAlgebra_amalgam_of_tailDoubleLR_of_faithful k φ₁ φ₂
    (fun t ↦ hMF _ _ _ _ t)
    (fun x ↦ (hagree x).mono_cut fun _ ↦ le_max_left _ _) hρ hΛ

end TailRecognition

/-- **Gelfand--Naimark with the dimension clause the repair needs.**  The landed
`SeparableFaithfulRepresentationStatement`, which is a theorem, together with
`¬ FiniteDimensional ℂ H`.  Owed; the module docstring gives two routes. -/
def SeparableFaithfulInfiniteRepresentationStatement : Prop :=
  ∀ (B : Type w) [CStarAlgebra B] [Nontrivial B]
    [TopologicalSpace.SeparableSpace B],
    ∃ (H : Type) (hgroup : NormedAddCommGroup H),
      letI : NormedAddCommGroup H := hgroup
      ∃ hinner : InnerProductSpace ℂ H,
        letI : InnerProductSpace ℂ H := hinner
        ∃ (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H)
          (_ : ¬ FiniteDimensional ℂ H)
          (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)), Function.Injective π

end

end ShulmanFill
end GroupApproximation
