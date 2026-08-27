import GroupApproximation.Kazhdan.KazhdanFixedSpace
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Averaging finite orthogonal group actions

This is the elementary Reynolds operator for a finite group acting on a real
inner-product space.  It is constructed as a literal finite sum and shown to
land in the fixed subspace.
-/

namespace GroupApproximation

universe u v

namespace FiniteGroupAverage

variable {G : Type u} [Group G] [Finite G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The normalized average of the orbit of a vector under a finite group. -/
noncomputable def orbitAverage (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) : E := by
  letI := Fintype.ofFinite G
  exact (Nat.card G : ℝ)⁻¹ • ∑ g : G, rho g x

/-- A finite group's cardinality is positive. -/
theorem natCard_pos : 0 < Nat.card G :=
  Nat.card_pos

/-- Orbit averaging produces an invariant vector. -/
theorem orbitAverage_fixed (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) (h : G) :
    rho h (orbitAverage rho x) = orbitAverage rho x := by
  letI := Fintype.ofFinite G
  unfold orbitAverage
  rw [map_smul, map_sum]
  congr 1
  calc
    ∑ g : G, rho h (rho g x) = ∑ g : G, rho (h * g) x := by
      apply Finset.sum_congr rfl
      intro g _
      rw [map_mul]
      rfl
    _ = ∑ g : G, rho g x := by
      exact Fintype.sum_equiv (Equiv.mulLeft h)
        (fun g : G ↦ rho (h * g) x) (fun g : G ↦ rho g x) fun _ ↦ rfl

/-- A vector already fixed by the finite group is unchanged by averaging. -/
theorem orbitAverage_eq_self_of_fixed
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) {x : E}
    (hx : ∀ g : G, rho g x = x) :
    orbitAverage rho x = x := by
  letI := Fintype.ofFinite G
  unfold orbitAverage
  simp_rw [hx]
  rw [Finset.sum_const]
  rw [Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
    Nat.card_eq_fintype_card, smul_smul]
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  rw [inv_mul_cancel₀ hcard, one_smul]

/-- The average lies in the fixed subspace of the whole finite group. -/
theorem orbitAverage_mem_fixedSubspace
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    orbitAverage rho x ∈ KazhdanFixedSpace.fixedSubspace rho ⊤ := by
  rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
  intro g _
  exact orbitAverage_fixed rho x g

/-- Averaging does not change the inner product against an invariant
vector. -/
theorem inner_orbitAverage_eq_of_fixed_right
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x y : E)
    (hy : ∀ g : G, rho g y = y) :
    inner ℝ (orbitAverage rho x) y = inner ℝ x y := by
  letI := Fintype.ofFinite G
  unfold orbitAverage
  rw [real_inner_smul_left, sum_inner]
  have hterm : ∀ g : G, inner ℝ (rho g x) y = inner ℝ x y := by
    intro g
    calc
      inner ℝ (rho g x) y = inner ℝ (rho g x) (rho g y) := by rw [hy g]
      _ = inner ℝ x y := (rho g).inner_map_map x y
  simp_rw [hterm, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℝ]
  rw [Nat.card_eq_fintype_card]
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  simp only [smul_eq_mul]
  field_simp

/-- The finite Reynolds operator satisfies the exact Pythagorean identity.
In the conjugation representation on Hilbert--Schmidt matrices, this says
that distance to the recovered commutant is exactly the norm deficit of the
finite-group average. -/
theorem norm_sub_orbitAverage_sq
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖x - orbitAverage rho x‖ ^ 2 =
      ‖x‖ ^ 2 - ‖orbitAverage rho x‖ ^ 2 := by
  have havgFixed : ∀ g : G,
      rho g (orbitAverage rho x) = orbitAverage rho x := by
    intro g
    exact orbitAverage_fixed rho x g
  have hinner :
      inner ℝ x (orbitAverage rho x) =
        ‖orbitAverage rho x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    symm
    exact inner_orbitAverage_eq_of_fixed_right
      rho x (orbitAverage rho x) havgFixed
  rw [norm_sub_sq_real, hinner]
  ring

/-- Mean squared displacement under a finite orthogonal action is twice the
squared distance to the invariant subspace.  For conjugation on normalized
Hilbert--Schmidt matrices this is the exact mean commutator-energy formula. -/
noncomputable def meanSquaredDisplacement
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) : ℝ := by
  letI := Fintype.ofFinite G
  exact (Nat.card G : ℝ)⁻¹ * ∑ g : G, ‖rho g x - x‖ ^ 2

theorem mean_norm_rho_sub_sq
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    meanSquaredDisplacement rho x =
      2 * (‖x‖ ^ 2 - ‖orbitAverage rho x‖ ^ 2) := by
  letI := Fintype.ofFinite G
  unfold meanSquaredDisplacement
  have hterm : ∀ g : G,
      ‖rho g x - x‖ ^ 2 =
        2 * ‖x‖ ^ 2 - 2 * inner ℝ (rho g x) x := by
    intro g
    rw [norm_sub_sq_real, (rho g).norm_map]
    ring
  have havgInner :
      inner ℝ (orbitAverage rho x) x =
        ‖orbitAverage rho x‖ ^ 2 := by
    have havgFixed : ∀ g : G,
        rho g (orbitAverage rho x) = orbitAverage rho x := by
      intro g
      exact orbitAverage_fixed rho x g
    calc
      inner ℝ (orbitAverage rho x) x
          = inner ℝ x (orbitAverage rho x) := real_inner_comm _ _
      _ = inner ℝ (orbitAverage rho x) (orbitAverage rho x) :=
        (inner_orbitAverage_eq_of_fixed_right
          rho x (orbitAverage rho x) havgFixed).symm
      _ = ‖orbitAverage rho x‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hsumInner :
      (Nat.card G : ℝ)⁻¹ * ∑ g : G, inner ℝ (rho g x) x =
        ‖orbitAverage rho x‖ ^ 2 := by
    rw [← havgInner]
    unfold orbitAverage
    rw [real_inner_smul_left, sum_inner]
  rw [Finset.sum_congr rfl fun g _ ↦ hterm g,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℝ]
  simp only [smul_eq_mul]
  rw [Nat.card_eq_fintype_card]
  rw [← Finset.mul_sum]
  have hsumInner' :
      (Fintype.card G : ℝ)⁻¹ * ∑ g : G, inner ℝ (rho g x) x =
        ‖orbitAverage rho x‖ ^ 2 := by
    simpa [Nat.card_eq_fintype_card] using hsumInner
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  have hinv : (Fintype.card G : ℝ)⁻¹ * Fintype.card G = 1 :=
    inv_mul_cancel₀ hcard
  calc
    (Fintype.card G : ℝ)⁻¹ *
        (Fintype.card G * (2 * ‖x‖ ^ 2) -
          2 * ∑ g : G, inner ℝ (rho g x) x) =
      (Fintype.card G : ℝ)⁻¹ *
          (Fintype.card G * (2 * ‖x‖ ^ 2)) -
        (Fintype.card G : ℝ)⁻¹ *
          (2 * ∑ g : G, inner ℝ (rho g x) x) := by ring
    _ = ((Fintype.card G : ℝ)⁻¹ * Fintype.card G) *
          (2 * ‖x‖ ^ 2) -
        2 * ((Fintype.card G : ℝ)⁻¹ *
          ∑ g : G, inner ℝ (rho g x) x) := by ring
    _ = 2 * (‖x‖ ^ 2 - ‖orbitAverage rho x‖ ^ 2) := by
      rw [hinv, hsumInner']
      ring

/-- The literal finite orbit average is the Hilbert orthogonal projection
onto the invariant subspace. -/
theorem orbitAverage_eq_fixedProjection [CompleteSpace E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    orbitAverage rho x =
      (KazhdanFixedSpace.fixedProjection rho ⊤ x : E) := by
  let U := KazhdanFixedSpace.fixedSubspace rho ⊤
  letI : CompleteSpace U :=
    (KazhdanFixedSpace.isClosed_fixedSubspace rho ⊤).completeSpace_coe
  change orbitAverage rho x = U.starProjection x
  symm
  apply U.eq_starProjection_of_mem_orthogonal
  · exact orbitAverage_mem_fixedSubspace rho x
  · rw [Submodule.mem_orthogonal]
    intro y hy
    rw [inner_sub_right]
    have hyfixed' : ∀ g : G, rho g y = y := by
      intro g
      exact (KazhdanFixedSpace.mem_fixedSubspace_iff rho ⊤ y).mp hy
        g (Subgroup.mem_top g)
    rw [real_inner_comm x y, real_inner_comm (orbitAverage rho x) y,
      inner_orbitAverage_eq_of_fixed_right rho x y hyfixed']
    exact sub_self _

end FiniteGroupAverage
end GroupApproximation
