import GroupApproximation.Analysis.ShulmanFillNormingExistentialLiftFaithful
import GroupApproximation.Analysis.ShulmanFillNormingTailDoubleMF
import GroupApproximation.Analysis.ShulmanFillNormingTailPrinted

/-!
# Theorem 10 from the legacy unital tail package

`ShulmanFill.isMFAlgebra_amalgam_of_printedPair` derives MF-ness of the
symmetric double from `Theorem4PrintedPairStatement`, which is false.  This
module is the same conditional derivation from
`UnitalTailPairPackageStatement`.

The chain is the one it mirrors: double the two legs, transfer the agreement,
convert the faithfulness of the pair of limits, and glue.  `doubleLR`,
`tailNull_sub_doubleLR` and `isMFAlgebra_amalgam_of_tailGlue` do the first
three; `injective_pairRep_eval_of_injective` is reused unchanged from the
unshifted route, because it is about representations and not about lifts.

## The one input that is owed

`hD` --- MF-ness of the coordinate algebras --- is carried as a hypothesis, in
the same way the unshifted `isMFAlgebra_amalgam_of_glue` carries its own and
lets `Analysis/ShulmanFillNormingEllTwoTheorem10` discharge it.  Here it is named
`ShiftedPrintedMFStatement`, and its discharge at the printed models is owed.

What is known about that discharge, so that it does not have to be rediscovered:

* the engine is general --- `hasMFEmbedding_boundedMatrixSequence` is stated at
  an arbitrary `Y : ℕ → FiniteModel`, and `hasMFEmbedding_starStrongSubalgebra`
  at an arbitrary matrix family;
* `hasMFEmbedding_doubledEllTwoProduct` is *not*: it is stated at the literal
  `fun n ↦ DoubledModel EllTwoCoefficient n`, so it cannot be reused at
  `fun m ↦ … (m + c)` and its proof has to be re-run there;
* re-running it walls at a `synthInstance` budget on
  `Algebra ℂ ↥(BoundedCStarSequence …)` with the coordinate unfolded past every
  pin.  `HasMFEmbedding` asks only for `NonUnitalCStarAlgebra`, so that demand
  comes from the proof, not the statement, and routing the shifted side through
  the *source* of an injective hom avoids it;
* the four instances the unshifted argument runs on are all `local` and do not
  survive an import: `matrixCStarAlgebraForFlatten`, `partialOrderMatrixForFlatten`,
  `starOrderedRingMatrixForFlatten`, `cStarAlgebraDoubledEllTwo`;
* the natural such hom --- pad the shifted sequence with zeros below the cut ---
  needs a dependent transport, since `n - c + c = n` is propositional, so every
  clause needs an `obtain ⟨m, rfl⟩ : ∃ m, n = m + c` before it can be proved.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

section TailFaithful

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [Nontrivial (H →L[ℂ] H)]
variable [Nontrivial (BlockSpace H 2 →L[ℂ] BlockSpace H 2)]
variable {A : ℕ → Type} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]

-- The order the doubled models are built over is the SPECTRAL one, not a
-- generic `PartialOrder`: `Analysis/ShulmanFillNormingDoubledData` says at its
-- line 41 that its consumer discharges both binders with
-- `CStarAlgebra.spectralOrder` and `CStarAlgebra.spectralOrderedRing`, and a
-- generic binder here synthesizes a different term from the one the imported
-- lemmas were elaborated with.  Declared the way
-- `Manuscript/OneSidedMFRadical/TensorSynchronizationTraceCore` declares them.
noncomputable local instance spectralOrderCoefficient (n : ℕ) :
    PartialOrder (A n) := CStarAlgebra.spectralOrder (A n)

local instance spectralOrderedRingCoefficient (n : ℕ) :
    StarOrderedRing (A n) := CStarAlgebra.spectralOrderedRing (A n)
variable {ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
variable {hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖}
variable {hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)}
variable {C D : Type} [CStarAlgebra C] [CStarAlgebra D]
variable [TopologicalSpace.SeparableSpace D]
variable (k : C →⋆ₐ[ℂ] D) {ρ₁ ρ₂ : D →⋆ₐ[ℂ] (H →L[ℂ] H)}
variable [Nonempty (CStarAmalgamRepresentation k k)]

/-- **Theorem 10 from a pair of tail lifts and a faithful pair of limits.**  The
unshifted `isMFAlgebra_amalgam_of_doubleLR_of_faithful`, in the repaired
vocabulary. -/
theorem isMFAlgebra_amalgam_of_tailDoubleLR_of_faithful
    (φ₁ : StarStrongTailLift ι hnorm hone ρ₁)
    (φ₂ : StarStrongTailLift ι hnorm hone ρ₂)
    (hD : ∀ t, HasMFEmbedding (ShiftedD (doubledIota ι) (doubled_norm_le ι)
      (doubled_hone ι hone)
      (commonCut (StarStrongTailLift.doubleLR φ₁ φ₂)
        (StarStrongTailLift.doubleLR φ₂ φ₁)) t))
    (hagree : ∀ x : C, TailNull (commonCut φ₁ φ₂)
      (fun t ↦ φ₁.toFun t (k x) - φ₂.toFun t (k x)))
    (hρ : ρ₁.comp k = ρ₂.comp k)
    (hΛ : Function.Injective (universalCStarAmalgamEval k k
      (StarStrongAsymptoticLift.limitRep k hρ))) :
    IsMFAlgebra (UniversalCStarAmalgam k k) :=
  isMFAlgebra_amalgam_of_tailGlue k (StarStrongTailLift.doubleLR φ₁ φ₂)
    (StarStrongTailLift.doubleLR φ₂ φ₁) hD
    (fun x ↦ tailNull_sub_doubleLR k φ₁ φ₂ _ x
      ((hagree x).mono_cut fun _ ↦ le_max_left _ _))
    (pairRep_comp_eq k hρ)
    (injective_pairRep_eval_of_injective k hρ hΛ)

end TailFaithful

section TailPrinted

/-- **The coordinate algebras of the repaired route are MF at the printed
models.**  Carried as a named input, exactly as the unshifted route carries
`hD`; its discharge is owed, and the module docstring records what is known
about it. -/
def ShiftedPrintedMFStatement : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ι : ∀ n, DoubledModel EllTwoCoefficient n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hnorm : ∀ (n : ℕ) (x : DoubledModel EllTwoCoefficient n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto
      (fun n ↦ ι n (1 : DoubledModel EllTwoCoefficient n) v) atTop (𝓝 v))
    (c : ℕ → ℕ) (t : ℕ),
    HasMFEmbedding (ShiftedD ι hnorm hone c t)

end TailPrinted

end

end ShulmanFill
end GroupApproximation
