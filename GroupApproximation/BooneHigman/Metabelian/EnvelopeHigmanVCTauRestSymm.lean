import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauDecompReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# The `p ↔ q` symmetry of the decomposition statement (lane bh-met-92e)

The cone swap does not depend on the order of its two words
(`higmanVCTauComm_coneSwap_comm`).  Transported along it:

* option A and flexible A of `(q p)` are option A and flexible A of `(p q)`;
* option E of `(q p)` is option R of `(p q)` and conversely;
* flexible B of `(q p)` is flexible B of `(p q)` with the witnesses `p1, q1` swapped;
* hence `higmanVCTauEqTwo_Opt`, `higmanVCTauEqTwo_Known`, the forms `aba` and `sas`, and
  `higmanVCTauEqTwo_Decomp` are symmetric in `p ↔ q` (`higmanVCTauRest_decomp_symm`).

**Mirror cross family.**  `higmanVCTauRest_crossSwap_decomp`: the cross family with
`|p| = 2`, `|q| = 1` (`higmanVCTauDecomp_Cross q p x y`) decomposes, by the cross family of
`(q p)` (`higmanVCTauDecomp_cross_decomp`) and the symmetry.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Option A is symmetric in `p ↔ q`. -/
theorem higmanVCTauRest_optionA_symm {d : ℕ} {p q x y : List (Fin d)} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (h : higmanVCTauShort_OptionA d q p x y hqp hpq) :
    higmanVCTauShort_OptionA d p q x y hpq hqp := by
  unfold higmanVCTauShort_OptionA at h ⊢
  rw [higmanVCTauComm_coneSwap_comm hpq hqp] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_optionA_symm

/-- Flexible A is symmetric in `p ↔ q`. -/
theorem higmanVCTauRest_flexA_symm {d : ℕ} {p q x y : List (Fin d)} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (h : higmanVCTauComm_FlexA d q p x y hqp hpq) :
    higmanVCTauComm_FlexA d p q x y hpq hqp := by
  unfold higmanVCTauComm_FlexA at h ⊢
  rw [higmanVCTauComm_coneSwap_comm hpq hqp] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_flexA_symm

/-- Flexible B is symmetric in `p ↔ q` (swap the witnesses `p1, q1`). -/
theorem higmanVCTauRest_flexB_symm {d : ℕ} {p q x y x' y' : List (Fin d)}
    (h : higmanVCTauComm_FlexB d q p x y x' y') : higmanVCTauComm_FlexB d p q x y x' y' := by
  unfold higmanVCTauComm_FlexB at h ⊢
  obtain ⟨P, Q, X, Y, p1, q1, D1, D2, hPQ, hQP, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12⟩ := h
  exact ⟨P, Q, X, Y, q1, p1, D1, D2, hPQ, hQP, h1, h2, h3, h4, h5, h7, h6, h9, h8, h10, h11, h12⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_flexB_symm

/-- Option E of `(q p)` is option R of `(p q)`. -/
theorem higmanVCTauRest_optionE_symm {d : ℕ} {p q x y : List (Fin d)}
    (h : higmanVCTauShort_OptionE d q p x y) : higmanVCTauComm_OptionR d p q x y := by
  unfold higmanVCTauShort_OptionE at h
  unfold higmanVCTauComm_OptionR
  exact ⟨h.1, h.2.2, h.2.1⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_optionE_symm

/-- Option R of `(q p)` is option E of `(p q)`. -/
theorem higmanVCTauRest_optionR_symm {d : ℕ} {p q x y : List (Fin d)}
    (h : higmanVCTauComm_OptionR d q p x y) : higmanVCTauShort_OptionE d p q x y := by
  unfold higmanVCTauComm_OptionR at h
  unfold higmanVCTauShort_OptionE
  exact ⟨h.1, h.2.2, h.2.1⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_optionR_symm

/-- The five options are symmetric in `p ↔ q`. -/
theorem higmanVCTauRest_opt_symm {d : ℕ} {p q x y x' y' : List (Fin d)}
    (h : higmanVCTauEqTwo_Opt d q p x y x' y') : higmanVCTauEqTwo_Opt d p q x y x' y' := by
  unfold higmanVCTauEqTwo_Opt at h ⊢
  rcases h with ⟨h1, h2, h⟩ | h | h | ⟨h1, h2, h⟩ | h
  · exact Or.inl ⟨h2, h1, higmanVCTauRest_optionA_symm h2 h1 h⟩
  · exact Or.inr (Or.inr (Or.inl (higmanVCTauRest_optionE_symm h)))
  · exact Or.inr (Or.inl (higmanVCTauRest_optionR_symm h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h1, higmanVCTauRest_flexA_symm h2 h1 h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (higmanVCTauRest_flexB_symm h))))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_opt_symm

/-- Known at level `n` is symmetric in `p ↔ q`. -/
theorem higmanVCTauRest_known_symm {d n : ℕ} {p q x y x' y' : List (Fin d)}
    (h : higmanVCTauEqTwo_Known d n q p x y x' y') :
    higmanVCTauEqTwo_Known d n p q x y x' y' := by
  unfold higmanVCTauEqTwo_Known at h ⊢
  rcases h with h | h | h | ⟨h1, h2, h | h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, Or.inl (higmanVCTauRest_opt_symm h)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, h2, Or.inr (higmanVCTauRest_opt_symm h)⟩))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_known_symm

/-- The form `aba` is symmetric in `p ↔ q` (swap `b1, b2`). -/
theorem higmanVCTauRest_aba_symm {d n : ℕ} {p q x y x' y' : List (Fin d)}
    (h : higmanVCTauEqTwo_Aba d n q p x y x' y') : higmanVCTauEqTwo_Aba d n p q x y x' y' := by
  unfold higmanVCTauEqTwo_Aba at h ⊢
  obtain ⟨a1, a2, b1, b2, X1, Y1, X2, Y2, ha, ha', hb, hb', l1, l2, l3, l4, m1, m2, m3, m4, m5,
    m6, m7, m8, k1, k2, k3⟩ := h
  rw [← higmanVCTauComm_coneSwap_comm hb hb'] at m5 m6
  exact ⟨a1, a2, b2, b1, X1, Y1, X2, Y2, ha, ha', hb', hb, l1, l2, l4, l3, m2, m1, m3, m4, m5,
    m6, m7, m8, k1, higmanVCTauRest_known_symm k2, k3⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_aba_symm

/-- The form `sas` is symmetric in `p ↔ q`. -/
theorem higmanVCTauRest_sas_symm {d n : ℕ} {p q x y x' y' : List (Fin d)} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (h : higmanVCTauEqTwo_Sas d n q p x y x' y' hqp hpq) :
    higmanVCTauEqTwo_Sas d n p q x y x' y' hpq hqp := by
  unfold higmanVCTauEqTwo_Sas at h ⊢
  obtain ⟨a1, a2, c1, c2, X1, Y1, X2, Y2, ha, ha', hc, hc', l1, l2, l3, l4, m1, m2, m3, m4, m5,
    m6, m7, m8, k1, k2, k3⟩ := h
  rw [higmanVCTauComm_coneSwap_comm hpq hqp] at m1 m2 m5 m6
  exact ⟨a1, a2, c1, c2, X1, Y1, X2, Y2, ha, ha', hc, hc', l1, l2, l3, l4, m1, m2, m3, m4, m5,
    m6, m7, m8, k1, higmanVCTauRest_known_symm k2, k3⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_sas_symm

/-- **Symmetry.**  A decomposition of `((q p); (x, y) → (x', y'))` is one of
`((p q); (x, y) → (x', y'))`. -/
theorem higmanVCTauRest_decomp_symm {d n : ℕ} {p q x y x' y' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (h : higmanVCTauEqTwo_Decomp d n q p x y x' y' hqp hpq) :
    higmanVCTauEqTwo_Decomp d n p q x y x' y' hpq hqp := by
  unfold higmanVCTauEqTwo_Decomp at h ⊢
  rcases h with h | h
  · exact Or.inl (higmanVCTauRest_aba_symm h)
  · exact Or.inr (higmanVCTauRest_sas_symm hpq hqp h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_decomp_symm

/-- **The mirror cross family decomposes** (`|p| = 2`, `|q| = 1`). -/
theorem higmanVCTauRest_crossSwap_decomp {d n : ℕ} (hd : 1 < d) {p q x y x' y' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hC : higmanVCTauDecomp_Cross q p x y)
    (hx : x.length + y.length = n)
    (hs : ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3))
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y') :
    higmanVCTauEqTwo_Decomp d n p q x y x' y' hpq hqp := by
  rw [← higmanVCTauComm_coneSwap_comm hpq hqp] at hmx hmy
  exact higmanVCTauRest_decomp_symm hpq hqp
    (higmanVCTauDecomp_cross_decomp hd hqp hpq hC hx hs hmx hmy)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauRest_crossSwap_decomp

end GroupApproximation.BooneHigman.Metabelian.Envelope
