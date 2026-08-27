import GroupApproximation.Sofic.InvolutionCollapseCenter

/-!
# Delorme circumcenters for a general finite-packet cocycle

The circumcenter argument used by involution collapse does not depend on
commutativity or on involutions.  This file exposes its true interface: a
bounded sequence of displacement orbits, unitary coordinate actions, and a
vanishing cocycle defect.  It is the Guichardet primitive needed by the
noncommutative finite-packet route.
-/

namespace GroupApproximation
namespace FinitePacketDelormeCenter

open Matrix Ultralimit KazhdanCornerMatrices
open InvolutionCollapseCocycle InvolutionCollapseCenter
open scoped Matrix.Norms.L2Operator

attribute [local instance] InnerProductSpace.complexToReal

noncomputable section

variable {Γ : Type*} [Group Γ]
variable {Y : ℕ → Type*} [∀ n, Fintype (Y n)] [∀ n, DecidableEq (Y n)]

/-- A bounded almost-cocycle with bounded limiting profile has approximate
coboundary primitives on every prescribed finite mover set. -/
theorem exists_approximate_coboundary
    (U : ∀ n, Γ → Matrix (Y n) (Y n) ℂ)
    (hU : ∀ n a, U n a ∈ Matrix.unitaryGroup (Y n) ℂ)
    (O : Γ → ∀ n, EuclideanSpace ℂ (Y n × Y n))
    (hOb : ∀ γ, IsBoundedSeq (O γ))
    (hone : ∀ n, O 1 n = 0)
    (hdefect : ∀ a γ, seqNorm (fun n ↦
      O γ n - (adFlat (U n a) (O (a⁻¹ * γ) n) + O a n)) = 0)
    {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ γ, seqNormSq (O γ) ≤ R)
    (T : Finset Γ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ w : ∀ n, EuclideanSpace ℂ (Y n × Y n),
      IsBoundedSeq w ∧ seqNorm w ≤ Real.sqrt R + 1 ∧
      ∀ a ∈ T, seqNormSq (fun n ↦
        O a n - (w n - adFlat (U n a) (w n))) ≤ δ := by
  classical
  have hι : Nonempty Γ := ⟨1⟩
  set D : ℝ := Real.sqrt R with hD
  have hDnn : 0 ≤ D := Real.sqrt_nonneg R
  have hOD : ∀ γ, seqNorm (O γ) ≤ D := by
    intro γ
    have hsq : seqNorm (O γ) ^ 2 ≤ R := by
      rw [← seqNormSq_eq_sq (hOb γ)]
      exact hR γ
    have hnn : 0 ≤ seqNorm (O γ) := seqNorm_nonneg (hOb γ)
    rw [hD]
    nlinarith [Real.sq_sqrt hR0, Real.sqrt_nonneg R]
  have hρD : centerRadius O ≤ D := by
    have hzero : orbitRadius O (fun n ↦ 0) ≤ D := by
      apply orbitRadius_le hι
      intro γ
      have hneg : seqNorm (fun n ↦
          (0 : EuclideanSpace ℂ (Y n × Y n)) - O γ n) = seqNorm (O γ) := by
        have heq : (fun n ↦
            (0 : EuclideanSpace ℂ (Y n × Y n)) - O γ n) =
            fun n ↦ -(O γ n) := by
          funext n
          rw [zero_sub]
        rw [heq]
        exact seqNorm_neg (O γ)
      rw [hneg]
      exact hOD γ
    exact (centerRadius_le hι hOb hOD isBoundedSeq_zero).trans hzero
  have hρnn : 0 ≤ centerRadius O := by
    obtain ⟨γ⟩ := id hι
    refine le_csInf ⟨orbitRadius O (O γ), O γ, hOb γ, rfl⟩ ?_
    rintro r ⟨v, hv, rfl⟩
    exact orbitRadius_nonneg hι hOb hOD hv
  set δ' : ℝ := min 1 (δ / (4 * (2 * D + 1))) with hδ'
  have hδ'pos : 0 < δ' := by
    rw [hδ']
    refine lt_min one_pos ?_
    have h4D : (0 : ℝ) < 4 * (2 * D + 1) := by nlinarith [hDnn]
    exact div_pos hδ h4D
  obtain ⟨v, hv, hvrad⟩ := exists_near_center hι hOb hOD hδ'pos
  have hvnorm : seqNorm v ≤ Real.sqrt R + 1 := by
    have h1 : seqNorm v = seqNorm (fun n ↦ v n - O 1 n) := by
      apply seqNorm_congr_norm
      intro n
      rw [hone n, sub_zero]
    calc
      seqNorm v = seqNorm (fun n ↦ v n - O 1 n) := h1
      _ ≤ orbitRadius O v := le_orbitRadius hOb hOD hv 1
      _ ≤ centerRadius O + δ' := hvrad.le
      _ ≤ Real.sqrt R + 1 := by
        rw [hD] at hρD
        linarith [min_le_left (1 : ℝ) (δ / (4 * (2 * D + 1)))]
  refine ⟨v, hv, hvnorm, fun a haT ↦ ?_⟩
  set w' : ∀ n, EuclideanSpace ℂ (Y n × Y n) :=
    fun n ↦ adFlat (U n a) (v n) + O a n with hw'
  have hw'b : IsBoundedSeq w' := by
    obtain ⟨Cv, hCv⟩ := hv
    obtain ⟨Ca, hCa⟩ := hOb a
    refine ⟨Cv + Ca, fun n ↦ ?_⟩
    calc
      ‖w' n‖ ≤ ‖adFlat (U n a) (v n)‖ + ‖O a n‖ := norm_add_le _ _
      _ ≤ Cv + Ca := by
        rw [norm_adFlat (hU n a)]
        exact add_le_add (hCv n) (hCa n)
  have hw'rad : orbitRadius O w' ≤ centerRadius O + δ' := by
    apply orbitRadius_le hι
    intro γ
    set d : ∀ n, EuclideanSpace ℂ (Y n × Y n) :=
      fun n ↦ O γ n - (adFlat (U n a) (O (a⁻¹ * γ) n) + O a n) with hd
    have hdb : IsBoundedSeq d := by
      obtain ⟨Cγ, hCγ⟩ := hOb γ
      obtain ⟨Cμ, hCμ⟩ := hOb (a⁻¹ * γ)
      obtain ⟨Ca, hCa⟩ := hOb a
      refine ⟨Cγ + (Cμ + Ca), fun n ↦ ?_⟩
      calc
        ‖d n‖ ≤ ‖O γ n‖ +
            ‖adFlat (U n a) (O (a⁻¹ * γ) n) + O a n‖ := norm_sub_le _ _
        _ ≤ Cγ + (Cμ + Ca) := by
          refine add_le_add (hCγ n) ?_
          calc
            ‖adFlat (U n a) (O (a⁻¹ * γ) n) + O a n‖ ≤
                ‖adFlat (U n a) (O (a⁻¹ * γ) n)‖ + ‖O a n‖ :=
              norm_add_le _ _
            _ ≤ Cμ + Ca := by
              rw [norm_adFlat (hU n a)]
              exact add_le_add (hCμ n) (hCa n)
    have hdzero : seqNorm d = 0 := by
      simpa only [hd] using hdefect a γ
    have hsplit : (fun n ↦ w' n - O γ n) =
        fun n ↦ adFlat (U n a) (v n - O (a⁻¹ * γ) n) + (-(d n)) := by
      funext n
      rw [hw', hd, adFlat_sub]
      module
    have hisom : seqNorm (fun n ↦
        adFlat (U n a) (v n - O (a⁻¹ * γ) n)) =
        seqNorm (fun n ↦ v n - O (a⁻¹ * γ) n) := by
      apply seqNorm_congr_norm
      intro n
      exact norm_adFlat (hU n a) _
    have hactedBdd : IsBoundedSeq (fun n ↦
        adFlat (U n a) (v n - O (a⁻¹ * γ) n)) := by
      obtain ⟨C, hC⟩ := hv.sub (hOb (a⁻¹ * γ))
      exact ⟨C, fun n ↦ by rw [norm_adFlat (hU n a)]; exact hC n⟩
    have htriangle := seqNorm_add_le hactedBdd hdb.neg
    calc
      seqNorm (fun n ↦ w' n - O γ n) =
          seqNorm (fun n ↦
            adFlat (U n a) (v n - O (a⁻¹ * γ) n) + (-(d n))) := by
        rw [hsplit]
      _ ≤ seqNorm (fun n ↦ adFlat (U n a)
            (v n - O (a⁻¹ * γ) n)) + seqNorm (fun n ↦ -(d n)) := htriangle
      _ = seqNorm (fun n ↦ v n - O (a⁻¹ * γ) n) + 0 := by
        rw [hisom, seqNorm_neg, hdzero]
      _ ≤ orbitRadius O v := by
        rw [add_zero]
        exact le_orbitRadius hOb hOD hv (a⁻¹ * γ)
      _ ≤ centerRadius O + δ' := hvrad.le
  have hstab := seqNormSq_sub_le_of_near_center hι hOb hOD hv hw'b
    (ρ := centerRadius O + δ') hvrad.le hw'rad
  have hconv : (fun n ↦ O a n - (v n - adFlat (U n a) (v n))) =
      fun n ↦ -(v n - w' n) := by
    funext n
    simp only [hw']
    module
  rw [hconv, seqNormSq_neg]
  refine hstab.trans ?_
  have hδ'le : δ' ≤ δ / (4 * (2 * D + 1)) := min_le_right _ _
  have hδ'le1 : δ' ≤ 1 := min_le_left _ _
  have hexp : 4 * ((centerRadius O + δ') ^ 2 - centerRadius O ^ 2) =
      4 * δ' * (2 * centerRadius O + δ') := by ring
  rw [hexp]
  have hbound : 2 * centerRadius O + δ' ≤ 2 * D + 1 := by
    linarith [hρD, hδ'le1]
  calc
    4 * δ' * (2 * centerRadius O + δ') ≤ 4 * δ' * (2 * D + 1) := by
      have hnn : (0 : ℝ) ≤ 4 * δ' := by linarith [hδ'pos]
      nlinarith [hbound]
    _ ≤ 4 * (δ / (4 * (2 * D + 1))) * (2 * D + 1) := by
      have hpos : (0 : ℝ) < 2 * D + 1 := by linarith
      nlinarith [hδ'le, hpos]
    _ = δ := by
      have hne : (4 * (2 * D + 1)) ≠ 0 :=
        ne_of_gt (by nlinarith [hDnn] : (0 : ℝ) < 4 * (2 * D + 1))
      rw [show (4 : ℝ) * (δ / (4 * (2 * D + 1))) * (2 * D + 1) =
        δ * ((4 * (2 * D + 1)) / (4 * (2 * D + 1))) by ring,
        div_self hne, mul_one]

end

end FinitePacketDelormeCenter
end GroupApproximation
