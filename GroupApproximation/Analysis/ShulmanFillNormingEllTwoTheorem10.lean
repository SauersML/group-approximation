import GroupApproximation.Analysis.ShulmanFillNormingEllTwoModels
import GroupApproximation.Analysis.ShulmanFillNormingExistentialLiftFaithful

/-!
# Theorem 10 at the printed models, with `hD` discharged

`Analysis/ShulmanFillNormingExistentialLiftFaithful` reduces Shulman's Theorem
10 to four hypotheses: two asymptotic lifts of `ρ₁` and `ρ₂` into one `𝒟` on
`H`, their asymptotic agreement on `C`, faithfulness of the pair of limits on
`H`, and `hD` — MF-embeddability of the *doubled* `𝒟`.  This module removes the
last one, by taking the coefficient algebras to be Shulman's printed family.

`hD` is not available at a general MF coefficient family, and the obstruction is
recorded in the repository rather than guessed at.  The header of
`Analysis/ShulmanFillNormingProductMF` says why: the prefix block-diagonal
embedding of a bounded product is multiplicative on the nose only because the
coordinates are *matrix* algebras, so no representative is ever chosen; "for
general MF coordinate algebras the entries would be corona classes, each with
its own null condition, and the block diagonal of chosen representatives would
only be well defined if the choices were null uniformly in the coordinate,
which they are not."  A general product permanence statement is therefore not
elementary, and `HasMFEmbedding (∏ₙ A n)` from `∀ n, HasMFEmbedding (A n)` is
not a wiring step.

At the printed coefficient family it is already proved.
`Analysis/ShulmanFillNormingEllTwoModels.hasMFEmbedding_doubledEllTwoStarStrong`
gives `HasMFEmbedding (𝒟)` for the *doubled* printed models and **any**
embedding family `ι` — it constrains the coefficients, `EllTwoCoefficient n =
B(ℂ^{n+1})`, and nothing else.  Since `doubledIota ι` is exactly such a family
whenever `ι` embeds the printed coefficients, `hD` is discharged outright, and
`isMFAlgebra_amalgam_of_doubleLR_ellTwo` below is Theorem 10 with no MF
hypothesis on `𝒟` at all.

## The three instances re-enabled at the top

`Analysis/ShulmanFillNormingEllTwoModels` pins three instances as `local`, and
its own header records why each of them has to be pinned: left to the search,
`M₂` over `B(ℂ^{n+1})` reaches `CStarAlgebra` through the Loewner order and the
continuous functional calculus, and the `StarSubalgebra` coercion at the head of
a `𝒟` goal makes every candidate unify through it.  A `local instance` does not
travel through an import, so this module has to re-enable them — by `attribute`,
not by re-declaring copies.  Copies would be defeq but not identical, and the
instances baked into `hasMFEmbedding_doubledEllTwoStarStrong`'s type are the
ones that have to be matched.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

attribute [local instance] cStarAlgebraDoubledEllTwo
  cStarAlgebraDoubledEllTwoStarStrong
  nonUnitalCStarAlgebraDoubledEllTwoStarStrong

/-! ## `hD` at the printed coefficients -/

section PrintedModelMF

variable [∀ m, Nontrivial (DoubledModel EllTwoCoefficient m)]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable (ι : ∀ n, EllTwoCoefficient n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
variable (hone : ∀ v : H,
  Tendsto (fun n ↦ ι n (1 : EllTwoCoefficient n) v) atTop (𝓝 v))

/-- **The doubled `𝒟` at the printed coefficients is MF-embeddable.**  This is
`hasMFEmbedding_doubledEllTwoStarStrong` read at the doubled data of
`Analysis/ShulmanFillNormingDoubledData`: `doubledIota ι` is a family of
embeddings of the doubled printed models, which is all that lemma asks for. -/
theorem hasMFEmbedding_doubledEllTwo_of_coefficientModel :
    HasMFEmbedding (StarStrong.starStrongSubalgebra (doubledIota ι)
      (doubled_norm_le ι) (doubled_hone ι hone)) :=
  hasMFEmbedding_doubledEllTwoStarStrong (doubledIota ι) (doubled_norm_le ι)
    (doubled_hone ι hone)

/-! ## Theorem 10 -/

section Amalgam

variable (hnorm : ∀ (n : ℕ) (x : EllTwoCoefficient n), ‖ι n x‖ ≤ ‖x‖)
variable [Nontrivial (H →L[ℂ] H)]
variable [Nontrivial (BlockSpace H 2 →L[ℂ] BlockSpace H 2)]
variable {C D : Type} [CStarAlgebra C] [CStarAlgebra D]
variable [TopologicalSpace.SeparableSpace D]
variable (k : C →⋆ₐ[ℂ] D) {ρ₁ ρ₂ : D →⋆ₐ[ℂ] (H →L[ℂ] H)}
variable [Nonempty (CStarAmalgamRepresentation k k)]

/-- **Shulman's Theorem 10 at the printed models.**  Two asymptotic lifts of
`ρ₁` and `ρ₂` into one `𝒟` over the printed coefficients `B(ℂ^{n+1})`, agreeing
asymptotically on `C`, with the pair of limits faithful on `H`.

Every other hypothesis is gone.  The doubling, the flip and the doubled
faithfulness are internal to
`Analysis/ShulmanFillNormingExistentialLiftFaithful`, and `hD` is discharged
here by `hasMFEmbedding_doubledEllTwo_of_coefficientModel`.  So this is the
whole of Theorem 10 modulo the lifting direction of Theorem 4 — which is what
supplies `φ₁`, `φ₂` and their agreement. -/
theorem isMFAlgebra_amalgam_of_doubleLR_ellTwo
    (φ₁ : StarStrongAsymptoticLift ι hnorm hone ρ₁)
    (φ₂ : StarStrongAsymptoticLift ι hnorm hone ρ₂)
    (hagree : ∀ c : C, Tendsto
      (fun t ↦ ‖φ₁.toFun t (k c) - φ₂.toFun t (k c)‖) atTop (𝓝 0))
    (hρ : ρ₁.comp k = ρ₂.comp k)
    (hΛ : Function.Injective
      (universalCStarAmalgamEval k k (StarStrongAsymptoticLift.limitRep k hρ))) :
    IsMFAlgebra (UniversalCStarAmalgam k k) :=
  isMFAlgebra_amalgam_of_doubleLR_of_faithful ι hnorm hone k
    (hasMFEmbedding_doubledEllTwo_of_coefficientModel ι hone) φ₁ φ₂ hagree hρ hΛ

end Amalgam

end PrintedModelMF

end

end ShulmanFill
end GroupApproximation
