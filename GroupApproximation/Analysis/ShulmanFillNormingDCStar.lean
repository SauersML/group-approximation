import GroupApproximation.Analysis.ShulmanFillNormingAsymptoticMF

/-!
# `𝒟` as a C-star algebra in its own right

`StarStrong.starStrongSubalgebra` is a star subalgebra of the bounded product
and `StarStrong.starStrongSubalgebra_isClosed` shows it is norm closed, so it
is a C-star algebra; but the bundled class was never assembled, which is why
`Analysis/StarStrongMatrixSequencesShulman` only ever states `→⋆ₐ[ℂ]` maps
*into* it and never treats it as a coefficient algebra.

The gluing argument needs it as a coefficient algebra: the two legs of the
symmetric double become honest `*`-homomorphisms into the reduced product
`∏_t 𝒟 / ⨁_t 𝒟`, and that reduced product only exists once `𝒟` carries
`CStarAlgebra` and `Nontrivial`.  This module assembles both, in the shape
`Analysis/MFAlgebraAmalgamGenerated.compatibleGeneratedCStarAlgebra` uses for
the analogous corona subalgebra: every parent structure is the one instance
search already finds on the subtype, and only completeness has to be supplied,
from closedness.

Because both are `instance`s rather than `def`s, the parents they expose are
the subtype's own, so nothing downstream sees a second `Semiring` path.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

universe u

section DCStar

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]
variable (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
variable (hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖)
variable (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v))

/-- **`𝒟` is a C-star algebra.**  Every parent is the subtype's own; only
completeness needs an argument, and it is closedness in a complete ambient
space. -/
@[reducible] noncomputable instance starStrongCStarAlgebra :
    CStarAlgebra (StarStrong.starStrongSubalgebra ι hnorm hone) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace :=
    (StarStrong.starStrongSubalgebra_isClosed ι hnorm hone).completeSpace_coe
  toCStarRing := inferInstance
  toNormedAlgebra :=
    (StarStrong.starStrongSubalgebra ι hnorm hone).toSubalgebra.toNormedAlgebra
  toStarModule :=
    StarSubalgebra.starModule (StarStrong.starStrongSubalgebra ι hnorm hone)

/-- **`𝒟` is nontrivial.**  It contains the unit of the bounded product, which
is not the zero sequence because no coordinate algebra is trivial. -/
noncomputable instance nontrivialStarStrongSubalgebra :
    Nontrivial (StarStrong.starStrongSubalgebra ι hnorm hone) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  have hcoord :
      ((1 : StarStrong.starStrongSubalgebra ι hnorm hone) :
          StarStrong.BoundedStarSequence A) =
        ((0 : StarStrong.starStrongSubalgebra ι hnorm hone) :
          StarStrong.BoundedStarSequence A) :=
    congrArg Subtype.val h
  have hone' : (1 : StarStrong.BoundedStarSequence A) = 0 := hcoord
  exact one_ne_zero hone'

/-- The inclusion of `𝒟` in the bounded product is isometric, so the norm of a
member is the norm of the underlying sequence.  Recorded because every bound
in the gluing argument is stated at one level and used at the other. -/
theorem norm_coe_starStrongSubalgebra
    (x : StarStrong.starStrongSubalgebra ι hnorm hone) :
    ‖(x : StarStrong.BoundedStarSequence A)‖ = ‖x‖ := rfl

end DCStar

end

end ShulmanFill
end GroupApproximation
