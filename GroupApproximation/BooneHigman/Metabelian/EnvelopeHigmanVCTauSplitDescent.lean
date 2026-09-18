import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauSplitPair
import GroupApproximation.Meta.AxiomGuard

/-!
# The generalized descent identity for the canonical `τ` (lane bh-met-77f)

For `T := higmanVCTau_tau d` (lane bh-met-77e):

* `ψ_T (of p) = T p` for every pair `p` (`higmanVCTauSplit_psi_of`);
* the descent value does not depend on the fuel once the fuel exceeds `|v| + |w|`
  (`higmanVCTauSplit_val_fuel`);
* **generalized descent identity** (`higmanVCTauSplit_descent`): for every incomparable pair
  `(v, w)` which is not short (`¬ (|v| ≤ 2 ∧ |w| ≤ 2)`),
  `T (v, w) = T (P, Q) * T (X, Y) * T (P, Q)⁻¹` with `P, Q, X, Y := pP, pQ, pX, pY (v, w)`.
  Long pairs: definition plus fuel independence.  Pairs with both words of length `≤ 3`: the
  short conjugation relator `(P, Q, X, Y, v, w)` (`higmanVC_psi_short`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- On a short pair the canonical `τ` is the short letter. -/
theorem higmanVCTauSplit_tau_short (d : ℕ) (p : List (Fin d) × List (Fin d))
    (h : p.1.length ≤ 3 ∧ p.2.length ≤ 3) : higmanVCTau_tau d p = higmanVCTau_letter d p := by
  rw [higmanVCTau_tau, higmanVCTau_val_succ, if_pos h]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_tau_short

/-- `ψ_T` on any generator is the canonical `τ`. -/
theorem higmanVCTauSplit_psi_of (d : ℕ) (p : List (Fin d) × List (Fin d)) :
    higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of p) = higmanVCTau_tau d p := by
  rw [higmanVC_psi, FreeGroup.lift_apply_of, higmanVC_psiGen]
  by_cases h : p.1.length ≤ 3 ∧ p.2.length ≤ 3
  · rw [dif_pos h, higmanVCTauSplit_tau_short d p h, higmanVCTau_letter, higmanVC_psiGen,
      dif_pos h]
  · exact dif_neg h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_psi_of

/-- **Fuel independence** of the descent value. -/
theorem higmanVCTauSplit_val_fuel {d : ℕ} (hd : 1 < d) :
    ∀ n k : ℕ, ∀ v w : List (Fin d), v.length + w.length + 1 ≤ n →
      v.length + w.length + 1 ≤ k →
        higmanVCTau_val d n (v, w) = higmanVCTau_val d k (v, w) := by
  intro n
  induction n with
  | zero =>
    intro k v w hn _
    omega
  | succ n ih =>
    intro k v w hn hk
    cases k with
    | zero => omega
    | succ k =>
      rw [higmanVCTau_val_succ, higmanVCTau_val_succ]
      by_cases h1 : (v, w).1.length ≤ 3 ∧ (v, w).2.length ≤ 3
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : ¬ (v, w).1 <+: (v, w).2 ∧ ¬ (v, w).2 <+: (v, w).1
        · have h1' : ¬ (v.length ≤ 3 ∧ w.length ≤ 3) := h1
          have hs : ¬ (v.length ≤ 2 ∧ w.length ≤ 2) := by omega
          have hvw : ¬ v <+: w := h2.1
          have hwv : ¬ w <+: v := h2.2
          have hl := higmanVCTauSplit_pair_len hd hvw hwv hs
          rw [if_pos h2, if_pos h2,
            ih k (higmanVCTau_pX (v, w)) (higmanVCTau_pY (v, w)) (by omega) (by omega)]
        · rw [if_neg h2, if_neg h2]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_val_fuel

/-- Enough fuel computes the canonical `τ`. -/
theorem higmanVCTauSplit_val_eq_tau {d : ℕ} (hd : 1 < d) (n : ℕ) (v w : List (Fin d))
    (h : v.length + w.length + 1 ≤ n) : higmanVCTau_val d n (v, w) = higmanVCTau_tau d (v, w) :=
  higmanVCTauSplit_val_fuel hd n (v.length + w.length + 1) v w h le_rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_val_eq_tau

/-- **Generalized descent identity.** -/
theorem higmanVCTauSplit_descent {d : ℕ} (hd : 1 < d) {v w : List (Fin d)}
    (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) (hs : ¬ (v.length ≤ 2 ∧ w.length ≤ 2)) :
    higmanVCTau_tau d (v, w) =
      higmanVCTau_tau d (higmanVCTau_pP (v, w), higmanVCTau_pQ (v, w)) *
        higmanVCTau_tau d (higmanVCTau_pX (v, w), higmanVCTau_pY (v, w)) *
          (higmanVCTau_tau d (higmanVCTau_pP (v, w), higmanVCTau_pQ (v, w)))⁻¹ := by
  obtain ⟨⟨h1, h2⟩, hP, hQ⟩ := higmanVCTauSplit_pair_PQ hd hvw hwv hs
  obtain ⟨hmx, hmy⟩ := higmanVCTauSplit_pair_maps hd hvw hwv hs h1 h2
  obtain ⟨hxy, hyx⟩ := higmanVCTauSplit_pair_incomp hd hvw hwv hs
  obtain ⟨hX, hY, hXY⟩ := higmanVCTauSplit_pair_len hd hvw hwv hs
  have hP3 : (higmanVCTau_pP (v, w)).length ≤ 3 := by omega
  by_cases hsh : v.length ≤ 3 ∧ w.length ≤ 3
  · have hX3 : (higmanVCTau_pX (v, w)).length ≤ 3 := by omega
    have hY3 : (higmanVCTau_pY (v, w)).length ≤ 3 := by omega
    have hmem : FreeGroup.of (higmanVCTau_pP (v, w), higmanVCTau_pQ (v, w)) *
        FreeGroup.of (higmanVCTau_pX (v, w), higmanVCTau_pY (v, w)) *
          (FreeGroup.of (higmanVCTau_pP (v, w), higmanVCTau_pQ (v, w)))⁻¹ *
            (FreeGroup.of (v, w))⁻¹ ∈ higmanVC_rels d fun l => l.length ≤ 3 := by
      rw [higmanVC_rels, Set.mem_setOf_eq]
      exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, hP3, hQ, hX3, hY3, hsh.1, hsh.2, h1, h2,
        hmx, hmy, hxy, hyx, hvw, hwv, rfl⟩))
    have h' := higmanVC_psi_short (higmanVCTau_tau d) (by omega : 0 < d) hmem
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, higmanVCTauSplit_psi_of,
      higmanVCTauSplit_psi_of, higmanVCTauSplit_psi_of, mul_inv_eq_one] at h'
    exact h'.symm
  · have hsh' : ¬ ((v, w).1.length ≤ 3 ∧ (v, w).2.length ≤ 3) := hsh
    have hinc : ¬ (v, w).1 <+: (v, w).2 ∧ ¬ (v, w).2 <+: (v, w).1 := ⟨hvw, hwv⟩
    rw [higmanVCTauSplit_tau_short d (higmanVCTau_pP (v, w), higmanVCTau_pQ (v, w)) ⟨hP3, hQ⟩]
    show higmanVCTau_val d (v.length + w.length + 1) (v, w) = _
    rw [higmanVCTau_val_succ, if_neg hsh', if_pos hinc,
      higmanVCTauSplit_val_eq_tau hd (v.length + w.length) (higmanVCTau_pX (v, w))
        (higmanVCTau_pY (v, w)) (by omega)]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauSplit_descent

end GroupApproximation.BooneHigman.Metabelian.Envelope
