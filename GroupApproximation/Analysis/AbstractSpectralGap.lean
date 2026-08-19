import GroupApproximation.Analysis.GNSEigenvector
import GroupApproximation.Kazhdan.KazhdanEigenvalueBound

/-!
# The abstract Kazhdan spectral gap

For a Kazhdan pair `(Q, ε)` and a unitary representation of the group in
an arbitrary unital C-star algebra, the real spectrum of the unitary
average over a finite symmetric superset `S ⊇ Q` containing `1` meets
`(1 - ε²/(4|S|), 1)` in nothing: every real spectral value other than `1`
is at most the machine rate.

The chain: a spectral value yields a state annihilating `(m - μ)²`
(`SpectralStateWitness`), GNS turns it into a genuine eigenvector
(`GNSEigenvector`), unitaries act isometrically on the GNS space, the
representation realifies, and the projection argument of
`KazhdanEigenvalueBound` forbids the eigenvalue.

This is the β2 keystone of the strict-Kazhdan-compression program of
`notes/FORMALIZATION_DIRECTIVES_2026-08-15.md` §1: applied componentwise
over the universal representation family it gives the uniform spectral
gap that builds the Kazhdan projection in the maximal group C-star
algebra.
-/

namespace GroupApproximation
namespace AbstractSpectralGap

open GNSEigenvector SpectralStateWitness
open scoped ComplexOrder

noncomputable section

universe u v

section UnitaryMap

variable {A : Type*} {B : Type*} [Semiring A] [Algebra ℂ A] [StarMul A]
  [Semiring B] [Algebra ℂ B] [StarMul B]

/-- A unital star homomorphism maps unitaries to unitaries. -/
def unitaryMap (π : A →⋆ₐ[ℂ] B) : unitary A →* unitary B where
  toFun u := ⟨π (u : A), by
    constructor
    · rw [← map_star, ← map_mul, u.property.1, map_one]
    · rw [← map_star, ← map_mul, u.property.2, map_one]⟩
  map_one' := Subtype.ext (map_one π)
  map_mul' u v := Subtype.ext (map_mul π _ _)

@[simp] theorem unitaryMap_coe (π : A →⋆ₐ[ℂ] B) (u : unitary A) :
    ((unitaryMap π u : unitary B) : B) = π (u : A) :=
  rfl

end UnitaryMap

section UnitaryAverage

variable {G : Type*} [Group G] {A : Type*} [CStarAlgebra A]

/-- The unitary average of a representation over a finite set. -/
def unitaryAverage (ρ : G →* unitary A) (S : Finset G) : A :=
  ((S.card : ℂ))⁻¹ • ∑ g ∈ S, ((ρ g : unitary A) : A)

theorem star_unitary_coe (ρ : G →* unitary A) (g : G) :
    star ((ρ g : unitary A) : A) = ((ρ g⁻¹ : unitary A) : A) := by
  have h1 : star (ρ g) = (ρ g)⁻¹ := rfl
  have h2 : ((star (ρ g) : unitary A) : A) = star ((ρ g : unitary A) : A) :=
    rfl
  rw [← h2, h1, ← map_inv]

/-- The average of a symmetric set is self-adjoint. -/
theorem isSelfAdjoint_unitaryAverage (ρ : G →* unitary A) {S : Finset G}
    (hS : ∀ g ∈ S, g⁻¹ ∈ S) :
    IsSelfAdjoint (unitaryAverage ρ S) := by
  unfold unitaryAverage
  have hconj : star ((S.card : ℂ))⁻¹ = ((S.card : ℂ))⁻¹ := by
    rw [star_inv₀, star_natCast]
  rw [IsSelfAdjoint, star_smul, star_sum, hconj]
  congr 1
  rw [show (∑ g ∈ S, star ((ρ g : unitary A) : A))
      = ∑ g ∈ S, ((ρ g⁻¹ : unitary A) : A) from
    Finset.sum_congr rfl fun g _ => star_unitary_coe ρ g]
  refine Finset.sum_nbij' (fun g => g⁻¹) (fun g => g⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro g hg; exact hS g hg
  · intro g hg; exact hS g hg
  · intro g _; exact inv_inv g
  · intro g _; exact inv_inv g
  · intro g _; rfl

end UnitaryAverage

section Realify

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A complex-linear isometric equivalence, restricted to a real one. -/
def realifyIsometryEquiv (e : H ≃ₗᵢ[ℂ] H) : H ≃ₗᵢ[ℝ] H where
  toLinearEquiv :=
    { toFun := e
      map_add' := map_add e
      map_smul' := fun r x => by
        show e (r • x) = r • e x
        rw [← algebraMap_smul ℂ r x, ← algebraMap_smul ℂ r (e x), map_smul]
      invFun := e.symm
      left_inv := e.toLinearEquiv.left_inv
      right_inv := e.toLinearEquiv.right_inv }
  norm_map' := fun x => e.norm_map x

@[simp] theorem realifyIsometryEquiv_apply (e : H ≃ₗᵢ[ℂ] H) (x : H) :
    realifyIsometryEquiv e x = e x :=
  rfl

/-- Realification as a monoid homomorphism. -/
def realifyIsometryHom : (H ≃ₗᵢ[ℂ] H) →* (H ≃ₗᵢ[ℝ] H) where
  toFun := realifyIsometryEquiv
  map_one' := by
    apply LinearIsometryEquiv.ext
    intro x
    rfl
  map_mul' := fun e f => by
    apply LinearIsometryEquiv.ext
    intro x
    rfl

end Realify

section Gap

variable {G : Type u} [Group G]
variable {A : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonnegSpectrumClass ℝ A]

/-- **The abstract spectral gap.** Every real spectral value of the
unitary average of a Kazhdan representation, other than `1`, is at most
`1 - ε²/(4|S|)`. -/
theorem unitaryAverage_spectrum_le
    (ρ : G →* unitary A) {Q : Finset G} {ε : ℝ}
    (hQ : IsKazhdanPair.{u, v} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) (hεone : ε ≤ 1)
    {μ : ℝ} (hμ : (μ : ℂ) ∈ spectrum ℂ (unitaryAverage ρ S))
    (hμ1 : μ ≠ 1) :
    μ ≤ 1 - ε ^ 2 / (4 * S.card) := by
  classical
  set m : A := unitaryAverage ρ S with hm
  have hsa : IsSelfAdjoint m := isSelfAdjoint_unitaryAverage ρ hsymm
  obtain ⟨Φ, hΦ1, hΦkill⟩ := exists_state_annihilating m hsa hμ
  set ξ : Φ.GNS := gnsCyclic Φ with hξ
  have hξnorm : ‖ξ‖ = 1 := norm_gnsCyclic Φ hΦ1
  have hξne : ξ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hξnorm
    exact one_ne_zero hξnorm.symm
  have heigC : Φ.gnsStarAlgHom m ξ = (μ : ℂ) • ξ :=
    gns_eigenvector Φ m hsa μ hΦkill
  letI : InnerProductSpace ℝ Φ.GNS := InnerProductSpace.rclikeToReal ℂ Φ.GNS
  set ρU : G →* unitary (Φ.GNS →L[ℂ] Φ.GNS) :=
    (unitaryMap Φ.gnsStarAlgHom).comp ρ with hρU
  set σ : G →* (Φ.GNS ≃ₗᵢ[ℝ] Φ.GNS) :=
    (realifyIsometryHom).comp ((unitaryIsometryHom).comp ρU) with hσ
  have hsmulR : ∀ (r : ℝ) (v : Φ.GNS), (r : ℂ) • v = r • v := fun r v => by
    rw [show ((r : ℂ)) = algebraMap ℝ ℂ r by simp, algebraMap_smul]
  have havg : KazhdanProjection.averageOperator S σ ξ = μ • ξ := by
    rw [KazhdanProjection.averageOperator_apply]
    show ((S.card : ℝ))⁻¹ • ∑ g ∈ S, σ g ξ = μ • ξ
    have hterm : ∀ g ∈ S,
        σ g ξ = Φ.gnsStarAlgHom ((ρ g : unitary A) : A) ξ :=
      fun g _ => rfl
    rw [Finset.sum_congr rfl hterm]
    have hπm : Φ.gnsStarAlgHom m ξ
        = ((S.card : ℂ))⁻¹ •
          ∑ g ∈ S, Φ.gnsStarAlgHom ((ρ g : unitary A) : A) ξ := by
      rw [hm]
      show Φ.gnsStarAlgHom
          (((S.card : ℂ))⁻¹ • ∑ g ∈ S, ((ρ g : unitary A) : A)) ξ = _
      rw [map_smul, map_sum, smul_apply, sum_apply]
    calc ((S.card : ℝ))⁻¹ •
          ∑ g ∈ S, Φ.gnsStarAlgHom ((ρ g : unitary A) : A) ξ
        = ((((S.card : ℝ))⁻¹ : ℝ) : ℂ) •
          ∑ g ∈ S, Φ.gnsStarAlgHom ((ρ g : unitary A) : A) ξ :=
          (hsmulR _ _).symm
      _ = ((S.card : ℂ))⁻¹ •
          ∑ g ∈ S, Φ.gnsStarAlgHom ((ρ g : unitary A) : A) ξ := by
          congr 1
          push_cast
          ring
      _ = Φ.gnsStarAlgHom m ξ := hπm.symm
      _ = (μ : ℂ) • ξ := heigC
      _ = μ • ξ := hsmulR μ ξ
  exact KazhdanEigenvalueBound.eigenvalue_le_of_ne_one hQ S hQS hone hεone
    σ hξne hμ1 havg

end Gap

end

end AbstractSpectralGap
end GroupApproximation
