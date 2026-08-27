import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Analysis.StarStrongMatrixSequencesAlgebra

/-!
# Shulman's lifting criterion, as named statements

`StarStrongMatrixSequencesAlgebra` builds the algebra `𝒟` of `*`-strongly
convergent bounded sequences and the limit map `q : 𝒟 → B(H)`.  Shulman's
criterion is what `𝒟` was built for: it reads MF-ness of a separable C-star
algebra off the liftability of its representations through `q`.

Both statements below are **named `Prop`s, not theorems**.  They are recorded
here so that the object they quantify over is the one this repository builds,
and so that a proof can be attached to a statement that already type-checks
against `𝒟` and `q`.

## The criterion, and where the faithfulness goes

The forward direction is the useful one and it is where `ker q ⊇ ⨁ₙ Mₙ` is
used.  Suppose `π : A → B(H)` is faithful and lifts to `ρ : A → 𝒟`.  Compose
`ρ` with the quotient `∏ₙ Mₙ → ∏ₙ Mₙ / ⨁ₙ Mₙ`.  If `a` is killed by the
composite then `ρ a` is a norm-null sequence, so `q (ρ a) = 0`
(`starStrongLimit_eq_zero_of_tendsto_norm_zero`), so `π a = 0`, so `a = 0`.
That is an embedding of `A` into the matrix corona, which is MF-ness.

Faithfulness is therefore not decoration: a lift of the zero representation
carries no information, and the statement "every representation lifts" is not
the one the argument uses.  The criterion is stated for faithful `π` in both
directions.

## Attribution

The two statements are Shulman's Theorem 4 and the contractive form recorded
in his Remark 6, as reported to this lane; the second is stated here as "the
lift may be chosen contractive".  Neither is proved here, and neither should
be cited from this file until the statement has been checked against the
printed source -- in particular the exact hypotheses of Remark 6, which this
file records in the only form the lane received.
-/

namespace GroupApproximation
namespace StarStrong

open Filter Topology

noncomputable section

/-- **Shulman, Theorem 4 (statement).**  A separable C-star algebra is MF
exactly when every faithful representation on `H` lifts through `q` to a
`*`-homomorphism into `𝒟`. -/
def MFLiftingCharacterization : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {M : ℕ → Type} [∀ n, CStarAlgebra (M n)]
    (ι : ∀ n, M n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hnorm : ∀ (n : ℕ) (x : M n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : M n) v) atTop (𝓝 v))
    (A : Type) [CStarAlgebra A],
    IsMFAlgebra A ↔
      ∀ pi : A →⋆ₐ[ℂ] (H →L[ℂ] H), Function.Injective pi →
        ∃ rho : A →⋆ₐ[ℂ] starStrongSubalgebra ι hnorm hone,
          ∀ a : A, starStrongLimitHom ι hnorm hone (rho a) = pi a

/-- **Shulman, Remark 6 (statement).**  The contractive form: the lift may be
chosen contractive.  Recorded separately because the lift produced by the
criterion is a `*`-homomorphism of C-star algebras and so contractive on the
nose; what Remark 6 adds is that the contractive lift may be demanded of the
*data*, before the homomorphism property is known. -/
def MFContractiveLiftingCharacterization : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {M : ℕ → Type} [∀ n, CStarAlgebra (M n)]
    (ι : ∀ n, M n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hnorm : ∀ (n : ℕ) (x : M n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : M n) v) atTop (𝓝 v))
    (A : Type) [CStarAlgebra A],
    IsMFAlgebra A ↔
      ∀ pi : A →⋆ₐ[ℂ] (H →L[ℂ] H), Function.Injective pi →
        ∃ rho : A →⋆ₐ[ℂ] starStrongSubalgebra ι hnorm hone,
          (∀ a : A, starStrongLimitHom ι hnorm hone (rho a) = pi a) ∧
            ∀ a : A, ‖rho a‖ ≤ ‖a‖

end

end StarStrong
end GroupApproximation
