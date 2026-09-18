import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauVal
import GroupApproximation.Meta.AxiomGuard

/-!
# The canonical `τ` kills the comparable and involution relators (lane bh-met-77e)

For `τ := higmanVCTau_tau d`, the homomorphism `ψ_τ` kills every comparable-letter relator
`(v, w)` (`higmanVCTau_psi_comparable`) and every involution relator `(v, w)²`
(`higmanVCTau_psi_sq`) of `higmanVC_rels d P`, for all words `v`, `w` of any length.  Short
pairs use the letter relators of lane bh-met-77; long pairs use the descent value: a long
comparable pair has value `1`, and the value of a long incomparable pair is a conjugate of a
value of smaller fuel, so squares vanish by induction on the fuel (`higmanVCTau_val_sq`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- A conjugate of an element of order dividing `2` has order dividing `2`. -/
theorem higmanVCTau_conj_sq {G : Type*} [Group G] (a b : G) (h : b * b = 1) :
    a * b * a⁻¹ * (a * b * a⁻¹) = 1 := by
  have hb : ∀ x : G, b * (b * x) = x := fun x => by rw [← mul_assoc, h, one_mul]
  simp only [mul_assoc, inv_mul_cancel_left, hb, mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_conj_sq

/-- The class of a short letter has order dividing `2`. -/
theorem higmanVCTau_letter_sq (d : ℕ) (p : List (Fin d) × List (Fin d)) :
    higmanVCTau_letter d p * higmanVCTau_letter d p = 1 := by
  unfold higmanVCTau_letter higmanVC_psiGen
  by_cases h : p.1.length ≤ 3 ∧ p.2.length ≤ 3
  · rw [dif_pos h]
    exact (map_mul (higmanVC_mk d) _ _).symm.trans
      (higmanVC_mk_rel (higmanVFP_letter_sq_mem h.1 h.2))
  · rw [dif_neg h, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_letter_sq

/-- Every descent value has order dividing `2`. -/
theorem higmanVCTau_val_sq (d n : ℕ) :
    ∀ p : List (Fin d) × List (Fin d), higmanVCTau_val d n p * higmanVCTau_val d n p = 1 := by
  induction n with
  | zero =>
    intro p
    rw [higmanVCTau_val_zero, mul_one]
  | succ n ih =>
    intro p
    rw [higmanVCTau_val_succ]
    by_cases h1 : p.1.length ≤ 3 ∧ p.2.length ≤ 3
    · rw [if_pos h1]
      exact higmanVCTau_letter_sq d p
    · rw [if_neg h1]
      by_cases h2 : ¬ p.1 <+: p.2 ∧ ¬ p.2 <+: p.1
      · rw [if_pos h2]
        exact higmanVCTau_conj_sq _ _ (ih _)
      · rw [if_neg h2, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_val_sq

/-- `ψ_τ` on a long generator is the canonical value. -/
theorem higmanVCTau_psi_of_long (d : ℕ) {v w : List (Fin d)}
    (h : ¬ (v.length ≤ 3 ∧ w.length ≤ 3)) :
    higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (v, w)) = higmanVCTau_tau d (v, w) := by
  rw [higmanVC_psi, FreeGroup.lift_apply_of, higmanVC_psiGen]
  exact dif_neg h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_psi_of_long

/-- **Comparable family.**  `ψ_τ` kills every comparable letter `(v, w)`. -/
theorem higmanVCTau_psi_comparable (d : ℕ) {v w : List (Fin d)}
    (hc : ¬ (¬ v <+: w ∧ ¬ w <+: v)) :
    higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (v, w)) = 1 := by
  by_cases h : v.length ≤ 3 ∧ w.length ≤ 3
  · rw [higmanVC_psi_of_short (higmanVCTau_tau d) h.1 h.2]
    exact higmanVC_mk_rel (higmanVFP_letter_comparable_mem h.1 h.2 hc)
  · rw [higmanVCTau_psi_of_long d h, higmanVCTau_tau, higmanVCTau_val_succ, if_neg h, if_neg hc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_psi_comparable

/-- **Involution family.**  `ψ_τ` kills every involution relator `(v, w)²`. -/
theorem higmanVCTau_psi_sq (d : ℕ) (v w : List (Fin d)) :
    higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (v, w) * FreeGroup.of (v, w)) = 1 := by
  rw [map_mul]
  by_cases h : v.length ≤ 3 ∧ w.length ≤ 3
  · rw [higmanVC_psi_of_short (higmanVCTau_tau d) h.1 h.2]
    exact (map_mul (higmanVC_mk d) _ _).symm.trans
      (higmanVC_mk_rel (higmanVFP_letter_sq_mem h.1 h.2))
  · rw [higmanVCTau_psi_of_long d h]
    exact higmanVCTau_val_sq d (v.length + w.length + 1) (v, w)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_psi_sq

end GroupApproximation.BooneHigman.Metabelian.Envelope
