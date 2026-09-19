import GroupApproximation.Analysis.ShulmanFillNormingExistentialLiftPrinted
import GroupApproximation.Analysis.ShulmanFillNormingTailAsymptoticMF

/-!
# Shulman's one-leg lifting theorem and the legacy tail-pair package

The earlier transcription merged Shulman's Theorem 4 with the two-leg
flip/Halmos argument used later in Theorem 10, and also required asymptotic
unitality.  Neither is in the definition cited by Theorem 4.  This module now
records Theorem 4 as a nonunital one-leg lift.  The old tail-pair package is
retained under an explicitly non-citation name only for the already-written
conditional tail-gluing development; recognition no longer assumes it.

## Printed coefficients

The coefficients stay pinned to `EllTwoCoefficient`.  That pinning is what makes
`hD` free (`Analysis/ShulmanFillNormingEllTwoTheorem10`), and
`Analysis/ShulmanFillNormingProductMF`'s header records that a general-coefficient
form could not: a product permanence statement for `HasMFEmbedding` is not
elementary.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

/-- **Shulman's Theorem 4, lifting direction, at the printed matrix models.**

For an infinite-dimensional separable Hilbert space, an MF algebra and one
representation, there is one contractive discrete asymptotic lift.  The lift
is deliberately nonunital: Shulman's definition asks for asymptotic linearity,
multiplicativity and adjoint preservation, but has no unit-defect clause.  No
second representation, common cut, or agreement-on-`C` clause belongs to this
statement; those arise only in the special stabilized flip construction in
the proof of Theorem 10. -/
def Theorem4OneLegStatement : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H],
    ¬ FiniteDimensional ℂ H →
    ∀ {B : Type} [CStarAlgebra B] [TopologicalSpace.SeparableSpace B],
      IsMFAlgebra B →
      ∀ ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H),
        ∃ (ι : ∀ n, EllTwoCoefficient n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
          (hnorm : ∀ (n : ℕ) (x : EllTwoCoefficient n), ‖ι n x‖ ≤ ‖x‖)
          (hone : ∀ v : H, Tendsto
            (fun n ↦ ι n (1 : EllTwoCoefficient n) v) atTop (nhds v)),
          Nonempty (NonUnitalStarStrongAsymptoticLift ι hnorm hone ρ)

/-- **The legacy unital two-leg tail package.**

This combines a stronger unital lift with the special agreement conclusion
of Lemma 9.  It is a useful conditional input for the old tail-gluing files,
but it is not Shulman's Theorem 4 and is not a recognition hypothesis.

For an infinite-dimensional separable Hilbert space `H`, a separable MF algebra
`B`, a subalgebra map `k : C →⋆ₐ[ℂ] B` and two faithful representations of `B`
on `H` agreeing on `C`, there is one family of contractive embeddings of the
printed models whose `𝒟` receives tail lifts of both representations, sharing a
cut and agreeing on `C` in the tail.

Compare `Theorem4PrintedPairStatement`, which is this statement with the three
repairs undone, and which is false. -/
def UnitalTailPairPackageStatement : Prop :=
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
theorem unitalTailPairPackage_of_printedPair_data
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

/-! ## The counter-models do not reach the repaired binder -/

/-- The space `not_theorem4PrintedPair` is instantiated at. -/
theorem finiteDimensional_euclidean_one :
    FiniteDimensional ℂ (EuclideanSpace ℂ (Fin 1)) := inferInstance

/-- The space `not_theorem4PrintedPair_of_character` is instantiated at. -/
theorem finiteDimensional_euclidean_two :
    FiniteDimensional ℂ (EuclideanSpace ℂ (Fin 2)) := inferInstance

/-- **Neither counter-model satisfies the repaired binder's hypotheses.**

Both are instantiated at a finite-dimensional `H` --- `ℂ¹` for
`not_theorem4PrintedPair` and `ℂ²` for `not_theorem4PrintedPair_of_character`
--- and `UnitalTailPairPackageStatement` asks for `¬ FiniteDimensional ℂ H`.  So
neither refutation transfers, and the two lemmas above are the whole of what can
be checked here.

The rest is an argument about a proof rather than about an instance, and is
recorded as such.  The character argument does not merely fail to apply at these
two spaces: it has no tail analogue at any `H`.  It runs by fixing a coordinate
`n` and reading the five defects of `(φ_t ·)ₙ` off the sup norm, and `TailNull`
bounds no fixed coordinate --- at every `t` past which it says anything, it says
it only of coordinates `n ≥ cut t`.  There is therefore no statement
corresponding to `exists_nonUnitalStarAlgHom_coord` to be made in the repaired
vocabulary, which is why the repair is the removal of the sup norm and not a
restriction on `H`. -/
theorem counterModels_are_finiteDimensional :
    FiniteDimensional ℂ (EuclideanSpace ℂ (Fin 1)) ∧
      FiniteDimensional ℂ (EuclideanSpace ℂ (Fin 2)) :=
  ⟨finiteDimensional_euclidean_one, finiteDimensional_euclidean_two⟩

end

end ShulmanFill
end GroupApproximation
