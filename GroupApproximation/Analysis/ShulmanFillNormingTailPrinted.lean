import GroupApproximation.Analysis.ShulmanFillNormingExistentialLiftPrinted
import GroupApproximation.Analysis.ShulmanFillNormingTailAsymptoticMF

/-!
# Theorem 4 at the printed models, repaired

`Theorem4PrintedPairStatement` is false: `Analysis/ShulmanFillNormingPrintedPairRefuted`
refutes it at a one-dimensional `H`, where the printed models have nowhere to
go, and `Analysis/ShulmanFillNormingPrintedPairCharacter` refutes it at every
`H`, because sup-norm defects at a finite-dimensional coefficient force a
character on `B`.  This module states the repaired binder.

## The three repairs

* **The defects move past a cut.**  The lifts are `StarStrongTailLift`s, so each
  defect is controlled only at coordinates `n ≥ cut t`, and the cut is data the
  witness chooses.  This is what the character argument loses its grip on:
  coordinate `0` is constrained by nothing.
* **The lift clause is the paper's.**  `q ∘ φ_t → π` pointwise, rather than the
  exact `q (φ_t b) = π b` that `Analysis/ShulmanFillNormingResiduallyFinite`
  records as stronger than the source.
* **`H` is infinite-dimensional.**  Without that the models cannot be placed at
  all, for the reason `not_theorem4PrintedPair` makes precise, and with it a
  separable `H` is `ℓ²` and `Analysis/EllTwoBlockFamily` builds the family the
  conclusion asks for.

The two legs are required to share a cut.  Nothing is lost: a construction
producing two legs produces them at the same stage, and the shared cut is what
lets the agreement clause be stated in the same tail vocabulary as the defects
rather than in the sup norm, which would be asking for more than Lemma 9 gives.

## What has not changed

The coefficients stay pinned to `EllTwoCoefficient`.  That pinning is what makes
`hD` free (`Analysis/ShulmanFillNormingEllTwoTheorem10`), and
`Analysis/ShulmanFillNormingProductMF`'s header records that a general-coefficient
form could not: a product permanence statement for `HasMFEmbedding` is not
elementary.  So the coefficients were never the thing to give up; the sup norm
was.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

/-- **Shulman's Theorem 4, Remark 6 and Lemma 9 as one package, at the printed
models, in the repaired vocabulary.**

For an infinite-dimensional separable Hilbert space `H`, a separable MF algebra
`B`, a subalgebra map `k : C →⋆ₐ[ℂ] B` and two faithful representations of `B`
on `H` agreeing on `C`, there is one family of contractive embeddings of the
printed models whose `𝒟` receives tail lifts of both representations, sharing a
cut and agreeing on `C` in the tail.

Compare `Theorem4PrintedPairStatement`, which is this statement with the three
repairs undone, and which is false. -/
def Theorem4TailPairStatement : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H],
    ¬ FiniteDimensional ℂ H →
    ∀ {C B : Type} [CStarAlgebra C] [CStarAlgebra B]
      [TopologicalSpace.SeparableSpace B] (k : C →⋆ₐ[ℂ] B),
      IsMFAlgebra B →
      ∀ ρ₁ ρ₂ : B →⋆ₐ[ℂ] (H →L[ℂ] H),
        Function.Injective ρ₁ → Function.Injective ρ₂ →
        ρ₁.comp k = ρ₂.comp k →
        ∃ (ι : ∀ n, EllTwoCoefficient n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
          (hnorm : ∀ (n : ℕ) (x : EllTwoCoefficient n), ‖ι n x‖ ≤ ‖x‖)
          (hone : ∀ v : H, Tendsto
            (fun n ↦ ι n (1 : EllTwoCoefficient n) v) atTop (𝓝 v))
          (φ₁ : StarStrongTailLift ι hnorm hone ρ₁)
          (φ₂ : StarStrongTailLift ι hnorm hone ρ₂),
          φ₁.cut = φ₂.cut ∧
            ∀ c : C, TailNull φ₁.cut
              (fun t ↦ φ₁.toFun t (k c) - φ₂.toFun t (k c))

/-- **The repaired binder asks for less than the refuted one, on the part they
share.**  A pair of lifts in the old vocabulary, with their agreement in the sup
norm, is a pair in the new one with the zero cut.

This is the honesty check on the repair: the two counter-models refute the old
statement, and this says the new statement is not a disguise for it — it is
implied by it, so it cannot be stronger. -/
theorem theorem4TailPair_of_printedPair_data
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {C B : Type} [CStarAlgebra C] [CStarAlgebra B]
    {k : C →⋆ₐ[ℂ] B} {ρ₁ ρ₂ : B →⋆ₐ[ℂ] (H →L[ℂ] H)}
    {ι : ∀ n, EllTwoCoefficient n →⋆ₙₐ[ℂ] (H →L[ℂ] H)}
    {hnorm : ∀ (n : ℕ) (x : EllTwoCoefficient n), ‖ι n x‖ ≤ ‖x‖}
    {hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : EllTwoCoefficient n) v) atTop (𝓝 v)}
    (φ₁ : StarStrongAsymptoticLift ι hnorm hone ρ₁)
    (φ₂ : StarStrongAsymptoticLift ι hnorm hone ρ₂)
    (hagree : ∀ c : C, Tendsto
      (fun t ↦ ‖φ₁.toFun t (k c) - φ₂.toFun t (k c)‖) atTop (𝓝 0)) :
    ∃ (ψ₁ : StarStrongTailLift ι hnorm hone ρ₁)
      (ψ₂ : StarStrongTailLift ι hnorm hone ρ₂),
      ψ₁.cut = ψ₂.cut ∧
        ∀ c : C, TailNull ψ₁.cut
          (fun t ↦ ψ₁.toFun t (k c) - ψ₂.toFun t (k c)) :=
  ⟨φ₁.toTail, φ₂.toTail, rfl,
    fun c ↦ tailNull_of_tendsto_norm _ (hagree c)⟩

end

end ShulmanFill
end GroupApproximation
