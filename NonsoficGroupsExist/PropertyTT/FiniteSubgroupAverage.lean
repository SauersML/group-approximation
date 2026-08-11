import NonsoficGroupsExist.PropertyTT.Basic
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Averaging a quasi-cocycle over a finite subgroup

For a genuine cocycle, restriction to a finite subgroup is a coboundary,
with transfer vector given by the average of the cocycle values.  The same
calculation for a quasi-cocycle has error at most its defect.  This elementary
lemma is one finite-stage ingredient in the abelian-normal-subgroup argument
behind Ozawa's relative `(T)` to relative `(TTT)` theorem.
-/

namespace NonsoficGroupsExist

open scoped InnerProductSpace

universe u v

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The transfer vector obtained by averaging quasi-cocycle values over a
finite subgroup. -/
noncomputable def quasiCocycleAverage (b : G → E) (A : Subgroup G)
    [Finite A] : E := by
  letI := Fintype.ofFinite A
  exact ((Nat.card A : ℂ)⁻¹) • ∑ a : A, b a

/-- The orthogonal averaging operator associated with a finite subgroup,
written directly as a finite sum. -/
noncomputable def unitarySubgroupAverage
    (rho : G →* (E ≃ₗᵢ[ℂ] E)) (A : Subgroup G) [Finite A] (z : E) : E := by
  letI := Fintype.ofFinite A
  exact ((Nat.card A : ℂ)⁻¹) • ∑ a : A, rho a z

/-- The norm of an average is bounded by a common bound for its summands. -/
theorem norm_cardInv_smul_sum_le {A : Type*} [Group A] [Fintype A]
    (f : A → E) {D : ℝ} (hf : ∀ a, ‖f a‖ ≤ D) :
    ‖((Nat.card A : ℂ)⁻¹ • ∑ a : A, f a)‖ ≤ D := by
  have hnNat : 0 < Nat.card A := Nat.card_pos
  have hnReal : (0 : ℝ) < Nat.card A := by exact_mod_cast hnNat
  have hsum : ‖∑ a : A, f a‖ ≤ (Nat.card A : ℝ) * D := by
    calc
      ‖∑ a : A, f a‖ ≤ ∑ a : A, ‖f a‖ := norm_sum_le _ _
      _ ≤ ∑ _a : A, D := Finset.sum_le_sum fun a _ ↦ hf a
      _ = (Nat.card A : ℝ) * D := by
        rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
        simp
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  calc
    (Nat.card A : ℝ)⁻¹ * ‖∑ a : A, f a‖ ≤
        (Nat.card A : ℝ)⁻¹ * ((Nat.card A : ℝ) * D) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hnReal.le)
    _ = D := by field_simp

/-- A finite unitary-group average is contractive. -/
theorem norm_unitarySubgroupAverage_le
    (rho : G →* (E ≃ₗᵢ[ℂ] E)) (A : Subgroup G) [Finite A] (z : E) :
    ‖unitarySubgroupAverage rho A z‖ ≤ ‖z‖ := by
  letI := Fintype.ofFinite A
  apply norm_cardInv_smul_sum_le
  intro a
  exact le_of_eq ((rho a).norm_map z)

/-- The finite subgroup average is fixed by every member of the subgroup. -/
theorem unitarySubgroupAverage_fixed
    (rho : G →* (E ≃ₗᵢ[ℂ] E)) (A : Subgroup G) [Finite A]
    (z : E) (x : A) :
    rho x (unitarySubgroupAverage rho A z) =
      unitarySubgroupAverage rho A z := by
  letI := Fintype.ofFinite A
  unfold unitarySubgroupAverage
  rw [map_smul, map_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft x)
    (fun a : A ↦ rho x (rho a z)) (fun a : A ↦ rho a z) fun a ↦ by
      change (rho x * rho a) z = rho (x * a) z
      rw [← rho.map_mul]

/-- Finite subgroup averaging is additive. -/
theorem unitarySubgroupAverage_sub
    (rho : G →* (E ≃ₗᵢ[ℂ] E)) (A : Subgroup G) [Finite A]
    (x y : E) :
    unitarySubgroupAverage rho A (x - y) =
      unitarySubgroupAverage rho A x - unitarySubgroupAverage rho A y := by
  letI := Fintype.ofFinite A
  unfold unitarySubgroupAverage
  simp_rw [map_sub, Finset.sum_sub_distrib, smul_sub]

/-- Averaging twice over the same finite subgroup changes nothing. -/
theorem unitarySubgroupAverage_idempotent
    (rho : G →* (E ≃ₗᵢ[ℂ] E)) (A : Subgroup G) [Finite A]
    (z : E) :
    unitarySubgroupAverage rho A (unitarySubgroupAverage rho A z) =
      unitarySubgroupAverage rho A z := by
  letI := Fintype.ofFinite A
  change ((Nat.card A : ℂ)⁻¹ •
      ∑ a : A, rho a (unitarySubgroupAverage rho A z)) =
    unitarySubgroupAverage rho A z
  simp_rw [unitarySubgroupAverage_fixed]
  rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hcard : (Fintype.card A : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hcard, one_smul]

/-- Averaging over a finite normal subgroup commutes with the ambient
unitary action. -/
theorem unitarySubgroupAverage_equivariant_of_normal
    (rho : G →* (E ≃ₗᵢ[ℂ] E)) (A : Subgroup G) [Finite A]
    [A.Normal] (z : E) (g : G) :
    unitarySubgroupAverage rho A (rho g z) =
      rho g (unitarySubgroupAverage rho A z) := by
  letI := Fintype.ofFinite A
  let conjugate : A ≃ A :=
    { toFun := fun a ↦
        ⟨g * a * g⁻¹, (inferInstance : A.Normal).conj_mem a a.property g⟩
      invFun := fun a ↦
        ⟨g⁻¹ * a * g, by
          simpa only [inv_inv] using
            (inferInstance : A.Normal).conj_mem a a.property g⁻¹⟩
      left_inv := by
        intro a
        apply Subtype.ext
        group
      right_inv := by
        intro a
        apply Subtype.ext
        group }
  unfold unitarySubgroupAverage
  rw [map_smul, map_sum]
  congr 1
  apply Fintype.sum_equiv conjugate.symm
      (fun a : A ↦ rho a (rho g z))
      (fun a : A ↦ rho g (rho a z))
  intro a
  change (rho a * rho g) z =
    (rho g * rho (conjugate.symm a)) z
  rw [← rho.map_mul, ← rho.map_mul]
  congr 2
  change (a : G) * g = g * (g⁻¹ * (a : G) * g)
  group

/-- Averaging turns the restriction of a quasi-cocycle to a finite subgroup
into a coboundary up to the original defect. -/
theorem norm_sub_average_sub_action_average_le
    {rho : G →* (E ≃ₗᵢ[ℂ] E)} {b : G → E} {D : ℝ}
    (hb : IsQuasiCocycle rho b D) (A : Subgroup G) [Finite A] (x : A) :
    ‖b x - (quasiCocycleAverage b A -
      rho x (quasiCocycleAverage b A))‖ ≤ D := by
  letI := Fintype.ofFinite A
  let err : A → E := fun a ↦ b (x * a) - b x - rho x (b a)
  have herr (a : A) : ‖err a‖ ≤ D := by
    exact hb.2 x a
  have havg : ‖((Nat.card A : ℂ)⁻¹ • ∑ a : A, err a)‖ ≤ D :=
    norm_cardInv_smul_sum_le err herr
  have htranslate : ∑ a : A, b (x * a) = ∑ a : A, b a := by
    exact Fintype.sum_equiv (Equiv.mulLeft x)
      (fun a : A ↦ b (x * a)) (fun a : A ↦ b a) fun _ ↦ rfl
  have hcard : (Fintype.card A : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hidentity :
      ((Nat.card A : ℂ)⁻¹ • ∑ a : A, err a) =
        -(b x - (quasiCocycleAverage b A -
          rho x (quasiCocycleAverage b A))) := by
    unfold quasiCocycleAverage
    dsimp [err]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, htranslate,
      map_smul, map_sum]
    rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
    rw [smul_sub, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ hcard, one_smul]
    module
  rw [← norm_neg (b x - (quasiCocycleAverage b A -
      rho x (quasiCocycleAverage b A))), ← hidentity]
  exact havg

/-- For a finite normal subgroup, its quasi-cocycle transfer average is
almost equivariant.  The comparison term is the coboundary of `b g` under
the subgroup averaging operator. -/
theorem norm_action_quasiCocycleAverage_sub_le
    {rho : G →* (E ≃ₗᵢ[ℂ] E)} {b : G → E} {D : ℝ}
    (hb : IsQuasiCocycle rho b D) (A : Subgroup G) [Finite A] [A.Normal]
    (g : G) :
    ‖rho g (quasiCocycleAverage b A) - quasiCocycleAverage b A -
        (unitarySubgroupAverage rho A (b g) - b g)‖ ≤ 2 * D := by
  letI := Fintype.ofFinite A
  let conjugate : A ≃ A :=
    { toFun := fun a ↦
        ⟨g * a * g⁻¹, (inferInstance : A.Normal).conj_mem a a.property g⟩
      invFun := fun a ↦
        ⟨g⁻¹ * a * g, by
          simpa only [inv_inv] using
            (inferInstance : A.Normal).conj_mem a a.property g⁻¹⟩
      left_inv := by
        intro a
        apply Subtype.ext
        group
      right_inv := by
        intro a
        apply Subtype.ext
        group }
  let err : A → E := fun a ↦
    (rho g (b a) - b (conjugate a)) -
      (rho (conjugate a) (b g) - b g)
  have herr (a : A) : ‖err a‖ ≤ 2 * D := by
    let e₁ : E := b (g * a) - b g - rho g (b a)
    let e₂ : E := b ((conjugate a : A) * g) - b (conjugate a) -
      rho (conjugate a) (b g)
    have he₁ : ‖e₁‖ ≤ D := hb.2 g a
    have he₂ : ‖e₂‖ ≤ D := hb.2 (conjugate a) g
    have hprod : (conjugate a : G) * g = g * a := by
      change (g * (a : G) * g⁻¹) * g = g * a
      group
    have hid : err a = e₂ - e₁ := by
      dsimp [err, e₁, e₂]
      rw [hprod]
      abel
    rw [hid]
    exact (norm_sub_le e₂ e₁).trans (by linarith)
  have havg :
      ‖((Nat.card A : ℂ)⁻¹ • ∑ a : A, err a)‖ ≤ 2 * D :=
    norm_cardInv_smul_sum_le err herr
  have hsumConjB : ∑ a : A, b (conjugate a) = ∑ a : A, b a := by
    exact Fintype.sum_equiv conjugate
      (fun a : A ↦ b (conjugate a)) (fun a : A ↦ b a) fun _ ↦ rfl
  have hsumConjAction :
      ∑ a : A, rho (conjugate a) (b g) = ∑ a : A, rho a (b g) := by
    exact Fintype.sum_equiv conjugate
      (fun a : A ↦ rho (conjugate a) (b g))
      (fun a : A ↦ rho a (b g)) fun _ ↦ rfl
  have hcard : (Fintype.card A : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hidentity :
      ((Nat.card A : ℂ)⁻¹ • ∑ a : A, err a) =
        rho g (quasiCocycleAverage b A) - quasiCocycleAverage b A -
          (unitarySubgroupAverage rho A (b g) - b g) := by
    unfold quasiCocycleAverage unitarySubgroupAverage
    dsimp [err]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib,
      hsumConjB, hsumConjAction, map_smul, map_sum]
    rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
    rw [smul_sub, smul_sub, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, inv_mul_cancel₀ hcard, one_smul]
  rw [← hidentity]
  exact havg

end NonsoficGroupsExist
