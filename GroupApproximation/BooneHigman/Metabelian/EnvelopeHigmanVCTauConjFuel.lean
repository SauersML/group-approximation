import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauConjWords
import GroupApproximation.Meta.AxiomGuard

/-!
# The descent identity for the canonical `τ` (lane bh-met-77g)

* `higmanVCTauConj_psi_of`: `ψ_τ (of r) = τ r` for every pair `r` (`τ := higmanVCTau_tau d`);
* `higmanVCTauConj_val_eq`: the descent value does not depend on the fuel once the fuel exceeds
  `|v| + |w|`;
* `higmanVCTauConj_tau_descent`: for a long incomparable pair `(p, q)` with descent
  `(P, Q, X, Y)`, `τ (p, q) = ℓ(P, Q) · τ (X, Y) · ℓ(P, Q)⁻¹`;
* two group identities used in the induction of the conjugation family.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `ψ_τ` of a short generator is its letter. -/
theorem higmanVCTauConj_psi_letter (d : ℕ) (r : List (Fin d) × List (Fin d))
    (h : r.1.length ≤ 3 ∧ r.2.length ≤ 3) :
    higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of r) = higmanVCTau_letter d r := by
  rw [higmanVC_psi_of_pair _ r h.1 h.2, higmanVCTau_letter, higmanVC_psiGen, dif_pos h]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_psi_letter

/-- The canonical value of a short pair is its letter. -/
theorem higmanVCTauConj_letter_eq_tau (d : ℕ) (r : List (Fin d) × List (Fin d))
    (h : r.1.length ≤ 3 ∧ r.2.length ≤ 3) : higmanVCTau_letter d r = higmanVCTau_tau d r := by
  rw [higmanVCTau_tau, higmanVCTau_val_succ, if_pos h]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_letter_eq_tau

/-- `ψ_τ` of every generator is the canonical value. -/
theorem higmanVCTauConj_psi_of (d : ℕ) (r : List (Fin d) × List (Fin d)) :
    higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of r) = higmanVCTau_tau d r := by
  by_cases h : r.1.length ≤ 3 ∧ r.2.length ≤ 3
  · rw [higmanVCTauConj_psi_letter d r h, higmanVCTauConj_letter_eq_tau d r h]
  · rw [higmanVC_psi, FreeGroup.lift_apply_of, higmanVC_psiGen]
    exact dif_neg h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_psi_of

/-- **Fuel independence.**  Any fuel `n > |v| + |w|` computes the canonical value. -/
theorem higmanVCTauConj_val_eq {d : ℕ} (hd : 1 < d) :
    ∀ N : ℕ, ∀ r : List (Fin d) × List (Fin d), r.1.length + r.2.length < N →
      ∀ n : ℕ, r.1.length + r.2.length < n → higmanVCTau_val d n r = higmanVCTau_tau d r := by
  intro N
  induction N with
  | zero => exact fun _ hr => absurd hr (Nat.not_lt_zero _)
  | succ N ih =>
    intro r hr n hn
    cases n with
    | zero => exact absurd hn (Nat.not_lt_zero _)
    | succ n =>
      rw [higmanVCTau_tau, higmanVCTau_val_succ, higmanVCTau_val_succ]
      by_cases h1 : r.1.length ≤ 3 ∧ r.2.length ≤ 3
      · simp only [if_pos h1]
      · by_cases h2 : ¬ r.1 <+: r.2 ∧ ¬ r.2 <+: r.1
        · have hlt : (higmanVCTau_pX r).length + (higmanVCTau_pY r).length <
              r.1.length + r.2.length := higmanVCTauConj_len_lt hd h1 h2.1 h2.2
          simp only [if_neg h1, if_pos h2]
          rw [ih (higmanVCTau_pX r, higmanVCTau_pY r)
              (show (higmanVCTau_pX r).length + (higmanVCTau_pY r).length < N by omega) n
              (show (higmanVCTau_pX r).length + (higmanVCTau_pY r).length < n by omega),
            ih (higmanVCTau_pX r, higmanVCTau_pY r)
              (show (higmanVCTau_pX r).length + (higmanVCTau_pY r).length < N by omega)
              (r.1.length + r.2.length) hlt]
        · simp only [if_neg h1, if_neg h2]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_val_eq

/-- **Descent identity.**  `τ (p, q) = ℓ(P, Q) · τ (X, Y) · ℓ(P, Q)⁻¹` for a long incomparable
pair. -/
theorem higmanVCTauConj_tau_descent {d : ℕ} (hd : 1 < d) {p q : List (Fin d)}
    (hlong : ¬ (p.length ≤ 3 ∧ q.length ≤ 3)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) :
    higmanVCTau_tau d (p, q) =
      higmanVCTau_letter d (higmanVCTau_pP (p, q), higmanVCTau_pQ (p, q)) *
        higmanVCTau_tau d (higmanVCTau_pX (p, q), higmanVCTau_pY (p, q)) *
          (higmanVCTau_letter d (higmanVCTau_pP (p, q), higmanVCTau_pQ (p, q)))⁻¹ := by
  have hlt := higmanVCTauConj_len_lt hd hlong hpq hqp
  have e : higmanVCTau_tau d (p, q) =
      higmanVCTau_val d (p.length + q.length + 1) (p, q) := rfl
  have hv := higmanVCTauConj_val_eq hd (p.length + q.length + 1)
    (higmanVCTau_pX (p, q), higmanVCTau_pY (p, q))
    (show (higmanVCTau_pX (p, q)).length + (higmanVCTau_pY (p, q)).length <
      p.length + q.length + 1 by omega)
    (p.length + q.length) hlt
  rw [e, higmanVCTau_val_succ,
    if_neg (show ¬ ((p, q).1.length ≤ 3 ∧ (p, q).2.length ≤ 3) from hlong),
    if_pos (show ¬ (p, q).1 <+: (p, q).2 ∧ ¬ (p, q).2 <+: (p, q).1 from ⟨hpq, hqp⟩), hv]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_tau_descent

/-- A conjugation relator is killed iff the conjugation identity holds in `higmanVC_Q d`. -/
theorem higmanVCTauConj_rel_iff (d : ℕ) (a b c : List (Fin d) × List (Fin d)) :
    higmanVC_psi d (higmanVCTau_tau d)
        (FreeGroup.of a * FreeGroup.of b * (FreeGroup.of a)⁻¹ * (FreeGroup.of c)⁻¹) = 1 ↔
      higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of a) *
          higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of b) *
          (higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of a))⁻¹ =
        higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of c) := by
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_rel_iff

/-- Undoing a conjugation by an involution. -/
theorem higmanVCTauConj_inv_conj {G : Type*} [Group G] {a b c : G} (ha : a * a = 1)
    (h : a * b * a⁻¹ = c) : b = a * (c * a) := by
  have hi : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb : ∀ x : G, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  rw [← h, hi]
  simp only [mul_assoc, ha, mul_one, hb]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_inv_conj

/-- The group identity of the induction step: conjugating by `L D L⁻¹` (with `L` an
involution) is conjugating by `L`, then `D`, then `L`. -/
theorem higmanVCTauConj_group {H : Type*} [Group H] {L D G G1 G2 G' : H} (hL : L * L = 1)
    (h1 : L * G * L⁻¹ = G1) (h2 : D * G1 * D⁻¹ = G2) (h3 : L * G' * L⁻¹ = G2) :
    L * D * L⁻¹ * G * (L * D * L⁻¹)⁻¹ = G' := by
  have hi : L⁻¹ = L := inv_eq_of_mul_eq_one_right hL
  have hb : ∀ x : H, L * (L * x) = x := fun x => by rw [← mul_assoc, hL, one_mul]
  rw [hi] at h1 h3
  rw [← h1, ← h3] at h2
  calc L * D * L⁻¹ * G * (L * D * L⁻¹)⁻¹ = L * (D * (L * G * L) * D⁻¹ * L) := by
        simp only [mul_inv_rev, hi, mul_assoc]
    _ = L * (L * G' * L * L) := by rw [h2]
    _ = G' := by simp only [mul_assoc, hL, mul_one, hb]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauConj_group

end GroupApproximation.BooneHigman.Metabelian.Envelope
