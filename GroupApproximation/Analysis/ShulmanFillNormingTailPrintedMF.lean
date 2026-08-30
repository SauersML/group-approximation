import GroupApproximation.Analysis.ShulmanFillNormingTailPad
import GroupApproximation.Analysis.ShulmanFillNormingTailRoute
import GroupApproximation.Analysis.ShulmanFillNormingPrintedPairCharacter

/-!
# The relabelled printed models are MF: the parked input discharged

`ShiftedPrintedMFStatement` asked `HasMFEmbedding` of each coordinate algebra
`ShiftedD ι hnorm hone c t` of the repaired route at the printed models.  The
route that failed — re-running the product argument at the shifted family —
died on the synthesis budget; the route here never re-runs anything.  The
padding homomorphism of `Analysis/ShulmanFillNormingTailPad` embeds the shifted
bounded product injectively into the unshifted one, whose MF-embeddability is
the landed `hasMFEmbedding_doubledEllTwoProduct`, and `ShiftedD` includes into
the shifted product by its subtype map.  Two backward transfers along
injective non-unital star homomorphisms finish it.

Nontriviality of the printed models is proved, not assumed:
`nontrivial_ellTwoCoefficient` plus `CStarMatrix.instNontrivial`.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology PolarLiftingGeneralCStar

noncomputable section

attribute [local instance] cStarAlgebraDoubledEllTwo
  matrixCStarAlgebraForFlatten
  partialOrderMatrixForFlatten
  starOrderedRingMatrixForFlatten

section GenericInclusion

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]
variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
variable (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
variable (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))

/-- The coordinate algebra's inclusion into the shifted bounded product, as a
non-unital star homomorphism.  Every clause is definitional, since `ShiftedD`'s
instances are the subalgebra's by `inferInstanceAs`. -/
def shiftedDInclusion (c : ℕ → ℕ) (t : ℕ) :
    ShiftedD ι hnorm hone c t →⋆ₙₐ[ℂ] StarStrong.BoundedStarSequence
      (shiftModel (A := A) (c t)) where
  toFun := ShiftedD.val ι hnorm hone c t
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

theorem shiftedDInclusion_injective (c : ℕ → ℕ) (t : ℕ) :
    Function.Injective (shiftedDInclusion ι hnorm hone c t) :=
  fun _ _ h ↦ Subtype.ext h

end GenericInclusion

/-- The printed models are nontrivial. -/
theorem nontrivial_doubledEllTwo (m : ℕ) :
    Nontrivial (DoubledModel EllTwoCoefficient m) :=
  haveI := nontrivial_ellTwoCoefficient m
  inferInstance

/-- **The parked input of the repaired route, discharged**: pad the shifted
bounded product into the unshifted one, and include the coordinate algebra
into the shifted product. -/
theorem shiftedPrintedMF : ShiftedPrintedMFStatement := by
  intro H _ _ _ ι hnorm hone c t
  haveI : ∀ m, Nontrivial (DoubledModel EllTwoCoefficient m) :=
    nontrivial_doubledEllTwo
  exact (hasMFEmbedding_of_pad hasMFEmbedding_doubledEllTwoProduct
      (c t)).of_injective_nonUnitalStarAlgHom
    (shiftedDInclusion ι hnorm hone c t)
    (shiftedDInclusion_injective ι hnorm hone c t)

/-- **The recognition statement from the repaired binder and the compatible
target alone.**  With the relabelled printed models proved MF, the repaired
route rests on exactly the two statements the manuscript cites. -/
theorem conjugateWordNorming_of_tailPair_of_compatible'
    (hT4 : Theorem4TailPairStatement)
    (hCTP : ShulmanSymmetricDouble.CompatibleTargetPairStatement) :
    ConjugateWordNormingStatement :=
  conjugateWordNorming_of_tailPair_of_compatible hT4 shiftedPrintedMF hCTP

end

end ShulmanFill
end GroupApproximation
