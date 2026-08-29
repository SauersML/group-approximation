import GroupApproximation.Analysis.ReducedProductMFPermanence
import GroupApproximation.Analysis.ShulmanFillNormingFamily
import GroupApproximation.Analysis.ShulmanFillNormingGluing
import GroupApproximation.Analysis.ShulmanFillNormingProductMF

/-!
# Shulman's Theorem 10, assembled from the gluing

`Analysis/ShulmanFillNormingGluing` produces a faithful `*`-homomorphism of the
symmetric double into `∏_t 𝒟 / ⨁_t 𝒟`.  `ReducedProductMFPermanence` turns that
into MF-ness once the coordinate algebra `𝒟` is MF-embeddable, and
`Analysis/ShulmanFillNormingProductMF` supplies exactly that at the printed
models: `𝒟` is a subalgebra of `∏ₙ M_{Yₙ}`, and prefix block diagonalization
embeds that bounded product in one norm-matrix corona.

So Theorem 10 is `isMFAlgebra_amalgam_of_glue` below, and its hypotheses are:

* two asymptotic lifts of `ρ₁` and `ρ₂` into `𝒟` — Shulman's Theorem 4 in the
  lifting direction, still owed, recorded as a binder here and never as a
  `Prop` definition;
* their agreement on `C`, which the flip supplies exactly
  (`ShulmanFill.conjugate_toFun_eq_of_commute`) as soon as the flip is a
  unitary of `𝒟` — the `M₂` amplification, still owed;
* faithfulness of `ρ₁ * ρ₂` on the double, which the symmetry supplies: for
  `π = π₁ * π₂` faithful, `ρ₁ = π₁ ⊕ π₂` and `ρ₂ = π₂ ⊕ π₁` give
  `ρ₁ * ρ₂ = π ⊕ (π ∘ flip)`.

## What the recognition debt now reads

`conjugateWordNorming` follows from Theorem 16
(`Analysis/ShulmanFillNormingCoronaRoute.conjugateWordNorming_of_shulmanTheorem16`,
an equivalence), Theorem 16 from Theorems 10 and 13
(`ShulmanSymmetricDouble.shulmanTheorem16_of_symmetricDouble`), Theorem 13 from
`ShulmanSymmetricDouble.CompatibleTargetPairStatement`, and Theorem 10 from the
three items above.  Two of those three are the same construction task — the
`M₂` amplification of the `𝒟` data, which supplies the flip — and the third is
the lifting direction of Theorem 4:

    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      {A : ℕ → Type} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]
      (ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
      (hnorm : ∀ n x, ‖ι n x‖ ≤ ‖x‖)
      (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)),
      (∀ n, HasMFEmbedding (A n)) →
      ∀ (B : Type) [CStarAlgebra B] [TopologicalSpace.SeparableSpace B],
        IsMFAlgebra B →
        ∀ (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)), Function.Injective π →
          Nonempty (ShulmanFill.StarStrongAsymptoticLift ι hnorm hone π)
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology PolarLiftingGeneralCStar

open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## `𝒟` is MF at the printed models -/

section MatrixModels

noncomputable local instance matrixModelCStarAlgebraForDoubleMF
    (Z : Type) [Fintype Z] [DecidableEq Z] [Nonempty Z] :
    CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
  [∀ n, Nontrivial (Matrix (Y n) (Y n) ℂ)]
variable (ι : ∀ n, Matrix (Y n) (Y n) ℂ →⋆ₙₐ[ℂ] (H →L[ℂ] H))
  (hnorm : ∀ (n : ℕ) (x : Matrix (Y n) (Y n) ℂ), ‖ι n x‖ ≤ ‖x‖)
  (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : Matrix (Y n) (Y n) ℂ) v)
    atTop (𝓝 v))

/-- **`𝒟` is MF-embeddable at the printed models.**  It is a subalgebra of the
bounded product of the matrix algebras, and that product embeds faithfully in
one norm-matrix corona by prefix block diagonalization. -/
theorem hasMFEmbedding_starStrongSubalgebra :
    HasMFEmbedding (StarStrong.starStrongSubalgebra ι hnorm hone) :=
  (hasMFEmbedding_boundedMatrixSequence Y).of_injective_nonUnitalStarAlgHom
    (StarStrong.starStrongSubalgebra ι hnorm hone).subtype.toNonUnitalStarAlgHom
    fun _ _ h ↦ Subtype.ext h

end MatrixModels

/-! ## Theorem 10 -/

section Double

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [Nontrivial (H →L[ℂ] H)]
variable {A : ℕ → Type} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]
variable {ι : ∀ n, A n →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
variable {hnorm : ∀ (n : ℕ) (x : A n), ‖ι n x‖ ≤ ‖x‖}
variable {hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : A n) v) atTop (𝓝 v)}
variable {C D : Type} [CStarAlgebra C] [CStarAlgebra D]
variable [TopologicalSpace.SeparableSpace D]
variable (k : C →⋆ₐ[ℂ] D) {ρ₁ ρ₂ : D →⋆ₐ[ℂ] (H →L[ℂ] H)}
variable [Nonempty (CStarAmalgamRepresentation k k)]

namespace StarStrongAsymptoticLift

/-- **Shulman's Theorem 10, from the gluing.**  Two asymptotic lifts agreeing
on `C` glue to a faithful homomorphism of the double into `∏_t 𝒟 / ⨁_t 𝒟`, and
a reduced product with MF coordinates makes a separable source MF.

Only the three hypotheses discussed in this module's header are left: the two
lifts, their agreement on `C`, and faithfulness of the pair of limits. -/
theorem isMFAlgebra_amalgam_of_glue
    (hD : HasMFEmbedding (StarStrong.starStrongSubalgebra ι hnorm hone))
    (φ₁ : StarStrongAsymptoticLift ι hnorm hone ρ₁)
    (φ₂ : StarStrongAsymptoticLift ι hnorm hone ρ₂)
    (hagree : ∀ c : C, Tendsto
      (fun t ↦ ‖φ₁.toFun t (k c) - φ₂.toFun t (k c)‖) atTop (𝓝 0))
    (hρ : ρ₁.comp k = ρ₂.comp k)
    (hΛ : Function.Injective (universalCStarAmalgamEval k k (limitRep k hρ))) :
    IsMFAlgebra (UniversalCStarAmalgam k k) := by
  haveI : TopologicalSpace.SeparableSpace (UniversalCStarAmalgam k k) :=
    separableSpace_universalCStarAmalgam k k
  exact ReducedProductMFPermanence.isMFAlgebra_of_injective_reducedProduct
    (fun _ : ℕ ↦ (StarStrong.starStrongSubalgebra ι hnorm hone))
    (universalCStarAmalgamEval k k
      (glueRep k φ₁ φ₂ hagree)).toNonUnitalStarAlgHom
    (injective_glueRep_eval k φ₁ φ₂ hagree hρ hΛ) (fun _ ↦ hD)

end StarStrongAsymptoticLift

end Double

end

end ShulmanFill
end GroupApproximation
