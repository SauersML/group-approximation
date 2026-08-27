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
open FinitePacketRankWeight InvolutionRankMass ScaledKazhdanTransport
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

/-- **The rank and mass profile is automatic after generator covariance.**

Here movers are indexed by the chosen finite generating set.  Compatibility
of their packet automorphisms with the orbit map turns the internally
constructed exact covariance into the hypotheses of the finite-packet word
bound.  Consequently both the integer rank estimate and its Frobenius-mass
counterpart are conclusions, not additional caller data. -/
theorem exists_exact_generator_packet_with_rank_bounds
    (B : OpAlmostRepresentation E)
    (packet : F →* E)
    (orbit : Γ → F)
    (S : Finset Γ)
    (hgen : WordMetric.IsSymmetricGeneratingSet (S : Set Γ))
    (mover : ↥S → E)
    (β : ↥S → F ≃* F)
    (hcov : ∀ a f,
      mover a * packet f * (mover a)⁻¹ = packet (β a f))
    (horbit : ∀ a : ↥S, ∀ g : Γ,
      β a (orbit g) = orbit ((a : Γ) * g)) :
    ∃ V : ∀ n, F →* Matrix.unitaryGroup (B.model n) ℂ,
      ∃ Uhat : ↥S → ∀ n, Matrix.unitaryGroup (B.model n) ℂ,
        (∀ f, QuotientGroup.mk (fun n ↦ V n f) =
          (OpAlmostRepresentation.coronaHom B) (packet f)) ∧
        (∀ a, (QuotientGroup.mk (Uhat a) :
          NormMatrixCoronaUnitary B.model) =
            (OpAlmostRepresentation.coronaHom B) (mover a)) ∧
        (∀ n a f, Uhat a n * V n f * (Uhat a n)⁻¹ = V n (β a f)) ∧
        (∀ n g,
          displacementRank
              (fun γ ↦ (V n (orbit γ) :
                Matrix (B.model n) (B.model n) ℂ)) g ≤
            WordMetric.wordNorm (S : Set Γ) g *
              generatorRankWeight
                (fun γ ↦ (V n (orbit γ) :
                  Matrix (B.model n) (B.model n) ℂ)) S) ∧
        (∀ n g,
          matMass
              ((V n (orbit g) : Matrix (B.model n) (B.model n) ℂ) -
                (V n (orbit 1) : Matrix (B.model n) (B.model n) ℂ)) ≤
            4 * WordMetric.wordNorm (S : Set Γ) g *
              generatorRankWeight
                (fun γ ↦ (V n (orbit γ) :
                  Matrix (B.model n) (B.model n) ℂ)) S) := by
  classical
  have hmodel : ∀ n, Nonempty (B.model n) :=
    fun n ↦ Fintype.card_pos_iff.mp (B.modelNonempty n)
  obtain ⟨V, Uhat, hVlift, hUlift, hcovExact⟩ :=
    exists_exact_covariant_coordinate_lifts_of_ambient
      hmodel (OpAlmostRepresentation.coronaHom B) packet mover β hcov
  refine ⟨V, Uhat, hVlift, hUlift, hcovExact, ?_, ?_⟩
  · intro n g
    let W : Γ → Matrix (B.model n) (B.model n) ℂ :=
      fun γ ↦ V n (orbit γ)
    let U : Γ → Matrix (B.model n) (B.model n) ℂ := fun γ ↦
      if hγ : γ ∈ S then Uhat ⟨γ, hγ⟩ n else 1
    have hU : ∀ a ∈ S, U a ∈ Matrix.unitaryGroup (B.model n) ℂ := by
      intro a ha
      simp only [U, dif_pos ha]
      exact (Uhat ⟨a, ha⟩ n).prop
    have hWcov : ∀ a ∈ S, ∀ x : Γ,
        W (a * x) = U a * W x * (U a)ᴴ := by
      intro a ha x
      have hc := hcovExact n ⟨a, ha⟩ (orbit x)
      have hcval := congrArg Subtype.val hc
      rw [horbit ⟨a, ha⟩ x] at hcval
      dsimp only [W, U]
      simp only [dif_pos ha]
      exact hcval.symm
    exact displacementRank_le_wordNorm_mul W U S hgen hU hWcov g
  · intro n g
    let W : Γ → Matrix (B.model n) (B.model n) ℂ :=
      fun γ ↦ V n (orbit γ)
    let U : Γ → Matrix (B.model n) (B.model n) ℂ := fun γ ↦
      if hγ : γ ∈ S then Uhat ⟨γ, hγ⟩ n else 1
    have hVunit : ∀ γ, W γ ∈ Matrix.unitaryGroup (B.model n) ℂ :=
      fun γ ↦ (V n (orbit γ)).prop
    have hU : ∀ a ∈ S, U a ∈ Matrix.unitaryGroup (B.model n) ℂ := by
      intro a ha
      simp only [U, dif_pos ha]
      exact (Uhat ⟨a, ha⟩ n).prop
    have hWcov : ∀ a ∈ S, ∀ x : Γ,
        W (a * x) = U a * W x * (U a)ᴴ := by
      intro a ha x
      have hc := hcovExact n ⟨a, ha⟩ (orbit x)
      have hcval := congrArg Subtype.val hc
      rw [horbit ⟨a, ha⟩ x] at hcval
      dsimp only [W, U]
      simp only [dif_pos ha]
      exact hcval.symm
    exact displacementMass_le_four_mul_wordNorm_mul_weight
      (hmodel n) W U S hgen hVunit hU hWcov g

end

end FinitePacketCoronaCollapse
end GroupApproximation
