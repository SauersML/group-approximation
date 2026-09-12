import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Analysis.StarStrongLimitNorm

/-!
# Shulman's lifting criterion, repaired and proved in the direction that is used

`StarStrongMatrixSequencesAlgebra` builds the algebra `𝒟` of `*`-strongly
convergent bounded sequences and the limit map `q : 𝒟 → B(H)`.  Shulman's
Theorem 4 reads MF-ness of a separable C-star algebra off the liftability of
its faithful representations through `q`.

## What this module used to say, and why it was wrong

It carried two named `Prop`s, `MFLiftingCharacterization` and
`MFContractiveLiftingCharacterization`, each a *biconditional*

    `∀ (ι : ∀ n, M n →⋆ₙₐ[ℂ] B(H)) (hnorm) (hone) (A), IsMFAlgebra A ↔ …`

quantified over an arbitrary family `M : ℕ → Type` of C-star algebras.  Both are
false, and the counterexample needs no analysis.  Take `H := ℂ` and `M n := ℂ`,
with `ι n` the canonical map `ℂ → (ℂ →L[ℂ] ℂ)`: it is contractive and unital, so
`hnorm` and `hone` hold.  A C-star algebra with no injective `*`-homomorphism
into `ℂ` — any noncommutative one, or any nonseparable commutative one such as
`lp (fun _ : ℕ ↦ ℂ) ∞` — satisfies the right-hand side vacuously, and the
nonseparable one is not MF, because `IsMFAlgebra` contains separability.  So the
`←` direction fails at that instance.

The `→` direction is not salvageable at arbitrary families either: at
`M n := ℂ` the algebra `𝒟` is commutative, so no noncommutative `A` lifts, MF or
not.  That direction is a statement about the *printed* family, `M n = M_{kₙ}`
with `ι n` the compressions of an exhausting sequence of finite-rank
projections, and it needs that family named before it can be true.

## What is here instead

The implication the recognition lane consumes, at models that are themselves MF,
which is the hypothesis the printed family satisfies:

* `MFOfStarStrongLiftStatement` (replacing `MFLiftingCharacterization`) — a
  separable algebra with a `*`-homomorphic lift into `𝒟` whose `*`-strong limit
  is a faithful representation is MF.  Proved, by `mfOfStarStrongLift`, from
  `StarStrongLimitNorm.isMFAlgebra_of_starStrongLift`.
* `ContractiveStarStrongLiftStatement` (replacing
  `MFContractiveLiftingCharacterization`) — Remark 6's contractivity is not an
  extra demand on the lift: *every* such lift is contractive into the bounded
  product, because a `*`-homomorphism of C-star algebras is.  Proved, by
  `contractiveStarStrongLift`.

Neither name has a consumer, so the rename costs nothing.  The direction still
owed is the printed one: from `A` MF to the existence of a lift with faithful
`*`-strong limit.  It is what Shulman's Theorem 10 *begins* with, and it needs
the concrete model `M_n ↪ B(ℓ²)`.

This module is in the root import list.  It was authored while builds were
suspended and has not been elaborated.
-/

namespace GroupApproximation
namespace StarStrong

open Filter Topology

noncomputable section

/-- **Shulman, Theorem 4, in the direction his Theorem 10 ends with.**  At
models that are MF, a separable algebra whose faithful representation lifts
through `q` is MF. -/
def MFOfStarStrongLiftStatement : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {M : ℕ → Type} [∀ n, CStarAlgebra (M n)]
    [∀ n, Nontrivial (M n)]
    (ι : ∀ n, M n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hnorm : ∀ (n : ℕ) (x : M n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : M n) v) atTop (𝓝 v)),
    (∀ n, HasMFEmbedding (M n)) →
      ∀ (A : Type) [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]
        (pi : A →⋆ₐ[ℂ] (H →L[ℂ] H)), Function.Injective pi →
        (∃ rho : A →⋆ₐ[ℂ] starStrongSubalgebra ι hnorm hone,
          ∀ a : A, starStrongLimitHom ι hnorm hone (rho a) = pi a) →
        IsMFAlgebra A

/-- The statement above, proved: a lift of a faithful representation is a
faithful `*`-strong limit, and `StarStrongLimitNorm` turns that into MF-ness. -/
theorem mfOfStarStrongLift : MFOfStarStrongLiftStatement := by
  intro H _ _ _ M _ _ ι hnorm hone hM A _ _ pi hpi hlift
  obtain ⟨rho, hrho⟩ := hlift
  refine isMFAlgebra_of_starStrongLift ι hnorm hone hM rho ?_
  intro a b hab
  apply hpi
  rw [← hrho a, ← hrho b]
  exact hab

/-- **Shulman, Remark 6, repaired.**  Contractivity of the lift is automatic:
the composite `A → 𝒟 ⊆ ∏ₙ Mₙ` is a `*`-homomorphism of C-star algebras. -/
def ContractiveStarStrongLiftStatement : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {M : ℕ → Type} [∀ n, CStarAlgebra (M n)]
    [∀ n, Nontrivial (M n)]
    (ι : ∀ n, M n →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hnorm : ∀ (n : ℕ) (x : M n), ‖ι n x‖ ≤ ‖x‖)
    (hone : ∀ v : H, Tendsto (fun n ↦ ι n (1 : M n) v) atTop (𝓝 v))
    (A : Type) [CStarAlgebra A]
    (rho : A →⋆ₐ[ℂ] starStrongSubalgebra ι hnorm hone) (a : A),
      ‖((rho a : starStrongSubalgebra ι hnorm hone) : BoundedStarSequence M)‖
        ≤ ‖a‖

/-- The statement above, proved. -/
theorem contractiveStarStrongLift : ContractiveStarStrongLiftStatement := by
  intro H _ _ _ M _ _ ι hnorm hone A _ rho a
  exact NonUnitalStarAlgHom.norm_apply_le
    (((starStrongSubalgebra ι hnorm hone).subtype).comp rho) a

end

end StarStrong
end GroupApproximation
