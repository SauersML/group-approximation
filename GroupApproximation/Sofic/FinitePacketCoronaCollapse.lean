import GroupApproximation.Sofic.FinitePacketCoronaCovariance
import GroupApproximation.Sofic.FinitePacketCollapseCore
import GroupApproximation.Stability.MixedApproximation

/-!
# The closed finite-packet corona frontier

This module joins exact packet/covariance lifting to the terminal integer-rank
contradiction.  Starting with an ambient operator-norm almost representation,
the coordinate packet representations and the corrected coordinate movers are
constructed internally.  If the remaining analytic transport statement gives
scaled-mass vanishing for the selected packet displacements, their integer
rank weight vanishes and every selected packet value equals the base value on
a common tail.

The implication in the last clause isolates the only remaining generic
finite-packet input: deriving scaled-mass vanishing from property `(T)`, the
one-sided compression, and the packet orbit relations.  Exactification and
covariance are not caller-supplied.
-/

namespace GroupApproximation
namespace FinitePacketCoronaCollapse

open Matrix FinitePacketCoronaCovariance FinitePacketCollapseCore
open InvolutionRankMass ScaledKazhdanTransport
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u v

variable {F : Type u} [Group F] [Fintype F]
variable {A : Type v} [Fintype A]
variable {Γ E : Type} [Group Γ] [Group E]

/-- **Exact covariance plus the terminal finite-packet collapse.**

The ambient almost representation supplies its own corona homomorphism.
Exact finite-group coordinates and corrected mover lifts are produced by
`exists_exact_covariant_coordinate_lifts_of_ambient`.  The final implication
then consumes only the rank-scaled vanishing statement and returns literal
tail equality of all selected packet values. -/
theorem exists_exact_covariant_coordinates_with_terminal_collapse
    (B : OpAlmostRepresentation E)
    (packet : F →* E)
    (mover : A → E)
    (β : A → F ≃* F)
    (hcov : ∀ a f,
      mover a * packet f * (mover a)⁻¹ = packet (β a f))
    (orbit : Γ → F)
    (S : Finset Γ)
    (hinv : ∀ γ, orbit γ * orbit γ = 1)
    (hbraid : ∀ a ∈ S,
      orbit a * orbit 1 * orbit a = orbit 1 * orbit a * orbit 1) :
    ∃ V : ∀ n, F →* Matrix.unitaryGroup (B.model n) ℂ,
      ∃ Uhat : A → ∀ n, Matrix.unitaryGroup (B.model n) ℂ,
        (∀ f, QuotientGroup.mk (fun n ↦ V n f) =
          (OpAlmostRepresentation.coronaHom B) (packet f)) ∧
        (∀ a, (QuotientGroup.mk (Uhat a) :
          NormMatrixCoronaUnitary B.model) =
            (OpAlmostRepresentation.coronaHom B) (mover a)) ∧
        (∀ n a f, Uhat a n * V n f * (Uhat a n)⁻¹ = V n (β a f)) ∧
        ((∀ a ∈ S,
            ScaledMassVanishing B
              (packetRankWeight B
                (fun n γ ↦ (V n (orbit γ) :
                  Matrix (B.model n) (B.model n) ℂ)) S)
              (fun n ↦
                (V n (orbit a) : Matrix (B.model n) (B.model n) ℂ) -
                (V n (orbit 1) : Matrix (B.model n) (B.model n) ℂ))) →
          ∃ N, ∀ n ≥ N, ∀ a ∈ S, V n (orbit a) = V n (orbit 1)) := by
  classical
  have hmodel : ∀ n, Nonempty (B.model n) :=
    fun n ↦ Fintype.card_pos_iff.mp (B.modelNonempty n)
  obtain ⟨V, Uhat, hVlift, hUlift, hcovExact⟩ :=
    exists_exact_covariant_coordinate_lifts_of_ambient
      hmodel (OpAlmostRepresentation.coronaHom B) packet mover β hcov
  refine ⟨V, Uhat, hVlift, hUlift, hcovExact, ?_⟩
  intro hvan
  let W : ∀ n, Γ → Matrix (B.model n) (B.model n) ℂ :=
    fun n γ ↦ V n (orbit γ)
  have hWinv : ∀ n γ, IsExactInvolution (W n γ) := by
    intro n γ
    letI : Nonempty (B.model n) := hmodel n
    dsimp only [W]
    have hsquare : V n (orbit γ) * V n (orbit γ) = 1 := by
      rw [← map_mul, hinv γ, map_one]
    have hselfInv : (V n (orbit γ))⁻¹ = V n (orbit γ) :=
      inv_eq_of_mul_eq_one_right hsquare
    constructor
    · calc
        ((V n (orbit γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ) =
            ((V n (orbit γ))⁻¹ : Matrix.unitaryGroup (B.model n) ℂ) := rfl
        _ = (V n (orbit γ) : Matrix (B.model n) (B.model n) ℂ) :=
          congrArg Subtype.val hselfInv
    · exact congrArg Subtype.val hsquare
  have hWbraid : ∀ n a, a ∈ S →
      W n a * W n 1 * W n a = W n 1 * W n a * W n 1 := by
    intro n a ha
    change
      (V n (orbit a) : Matrix (B.model n) (B.model n) ℂ) *
            V n (orbit 1) * V n (orbit a) =
        (V n (orbit 1) : Matrix (B.model n) (B.model n) ℂ) *
            V n (orbit a) * V n (orbit 1)
    have hbGroup :
        V n (orbit a) * V n (orbit 1) * V n (orbit a) =
          V n (orbit 1) * V n (orbit a) * V n (orbit 1) := by
      simpa only [map_mul] using congrArg (V n) (hbraid a ha)
    exact congrArg Subtype.val hbGroup
  have hvanW : ∀ a ∈ S,
      ScaledMassVanishing B (packetRankWeight B W S)
        (fun n ↦ W n a - W n 1) := by
    simpa only [W] using hvan
  obtain ⟨N, hN⟩ :=
    eventually_generator_eq_base_of_scaled_vanishing
      B W S hWinv hWbraid hvanW
  refine ⟨N, fun n hn a ha ↦ ?_⟩
  apply Subtype.ext
  simpa only [W] using hN n hn a ha

end

end FinitePacketCoronaCollapse
end GroupApproximation
