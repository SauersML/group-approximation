import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauDeepReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# Swapping the two words of both pairs (lane bh-met-77y)

Every hop predicate of lanes bh-met-77r / bh-met-77t is symmetric under exchanging the two
words of the source pair `(x, y)` and, simultaneously, of the target pair `(x', y')`.  These
lemmas transport Hop D and Hop CD from the mirrored instance `(s; (y, x) → (y', x'))` back to
`(s; (x, y) → (x', y'))` (used in `EnvelopeHigmanVCTauUnifShape`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

theorem higmanVCTauUnif_flexA_swap {d : ℕ} {p q x y : List (Fin d)} {hpq : ¬ p <+: q}
    {hqp : ¬ q <+: p} (h : higmanVCTauComm_FlexA d p q x y hpq hqp) :
    higmanVCTauComm_FlexA d p q y x hpq hqp := by
  obtain ⟨P, Q, X, Y, P', Q', X', Y', hPQ, hQP, hP, hQ, hXx, hYy, hC, hsP, hsQ, hP3, hQ3, hX,
    hY, hC'⟩ := h
  exact ⟨P, Q, Y, X, P', Q', Y', X', hPQ, hQP, hP, hQ, hYy, hXx, by omega, hsP, hsQ, hP3, hQ3,
    hY, hX, by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_flexA_swap

theorem higmanVCTauUnif_flexB_swap {d : ℕ} {p q x y x' y' : List (Fin d)}
    (h : higmanVCTauComm_FlexB d p q x y x' y') : higmanVCTauComm_FlexB d p q y x y' x' := by
  obtain ⟨P, Q, X, Y, p1, q1, D1, D2, hPQ, hQP, hP, hQ, hXx, hYy, hC, hp1, hq1, hp13, hq13, hD1,
    hD2, hC'⟩ := h
  exact ⟨P, Q, Y, X, p1, q1, D2, D1, hPQ, hQP, hP, hQ, hYy, hXx, by omega, hp1, hq1, hp13, hq13,
    hD2, hD1, by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_flexB_swap

theorem higmanVCTauUnif_easy_swap {d n : ℕ} {p q x y x' y' : List (Fin d)}
    (h : higmanVCTauLevel_Easy d n p q x y x' y') : higmanVCTauLevel_Easy d n p q y x y' x' := by
  obtain ⟨h1, h2, hc⟩ := h
  refine ⟨by omega, by omega, ?_⟩
  rcases hc with hc | hc | ⟨hpq, hqp, hc⟩ | hc | ⟨hpq, hqp, hc⟩ | hc
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl ⟨hpq, hqp, higmanVCTauUnif_flexA_swap hc⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (higmanVCTauUnif_flexB_swap hc))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hpq, hqp, higmanVCTauUnif_flexA_swap hc⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (higmanVCTauUnif_flexB_swap hc)))))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_easy_swap

theorem higmanVCTauUnif_hopA_swap {d n : ℕ} {p q x y x' y' : List (Fin d)} {hpq : ¬ p <+: q}
    {hqp : ¬ q <+: p} (h : higmanVCTauLevel_HopA d n p q x y x' y' hpq hqp) :
    higmanVCTauLevel_HopA d n p q y x y' x' hpq hqp := by
  obtain ⟨P, Q, X, Y, P', Q', X', Y', hPQ, hQP, hP, hQ, hXx, hYy, hC, hsP, hsQ, hP3, hQ3, hX,
    hY, hE⟩ := h
  exact ⟨P, Q, Y, X, P', Q', Y', X', hPQ, hQP, hP, hQ, hYy, hXx, by omega, hsP, hsQ, hP3, hQ3,
    hY, hX, higmanVCTauUnif_easy_swap hE⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_hopA_swap

theorem higmanVCTauUnif_hopC_swap {d n : ℕ} {p q x y x' y' : List (Fin d)}
    (h : higmanVCTauLevel_HopC d n p q x y x' y') : higmanVCTauLevel_HopC d n p q y x y' x' := by
  obtain ⟨R, S, p1, q1, x1, y1, x2, y2, hRS, hSR, hR, hS, hp, hq, hp1, hq1, hx, hy, hx', hy',
    e1, e2, e3⟩ := h
  exact ⟨R, S, p1, q1, y1, x1, y2, x2, hRS, hSR, hR, hS, hp, hq, hp1, hq1, hy, hx, hy', hx',
    higmanVCTauUnif_easy_swap e1, higmanVCTauUnif_easy_swap e2, higmanVCTauUnif_easy_swap e3⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_hopC_swap

theorem higmanVCTauUnif_leg_swap {d n : ℕ} {p q x y x' y' : List (Fin d)}
    (h : higmanVCTauDeep_Leg d n p q x y x' y') : higmanVCTauDeep_Leg d n p q y x y' x' := by
  rcases h with h | ⟨hA, hpq, hqp, hH⟩ | ⟨hA, hpq, hqp, hH⟩ | h
  · exact Or.inl (higmanVCTauUnif_easy_swap h)
  · exact Or.inr (Or.inl ⟨by omega, hpq, hqp, higmanVCTauUnif_hopA_swap hH⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, hpq, hqp, higmanVCTauUnif_hopA_swap hH⟩))
  · exact Or.inr (Or.inr (Or.inr (higmanVCTauUnif_hopC_swap h)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_leg_swap

theorem higmanVCTauUnif_hopD_swap {d n : ℕ} {p q x y x' y' : List (Fin d)}
    (h : higmanVCTauDeep_HopD d n p q x y x' y') : higmanVCTauDeep_HopD d n p q y x y' x' := by
  obtain ⟨p0, q0, a, h0, h0', hp, hq, hmx, hmy, hL, hsib⟩ := h
  refine ⟨p0, q0, a, h0, h0', hp, hq, hmy, hmx, higmanVCTauUnif_leg_swap hL, fun b hb => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hsib b hb
  exact ⟨h2, h1, higmanVCTauUnif_leg_swap h3⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_hopD_swap

theorem higmanVCTauUnif_dleg_swap {d n : ℕ} {p q x y x' y' : List (Fin d)}
    (h : higmanVCTauDeep_DLeg d n p q x y x' y') : higmanVCTauDeep_DLeg d n p q y x y' x' := by
  rcases h with h | h | h
  · exact Or.inl (higmanVCTauUnif_leg_swap h)
  · exact Or.inr (Or.inl (higmanVCTauUnif_hopD_swap h))
  · exact Or.inr (Or.inr (higmanVCTauUnif_hopD_swap h))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_dleg_swap

theorem higmanVCTauUnif_hopCD_swap {d n : ℕ} {p q x y x' y' : List (Fin d)}
    (h : higmanVCTauDeep_HopCD d n p q x y x' y') : higmanVCTauDeep_HopCD d n p q y x y' x' := by
  obtain ⟨R, S, p1, q1, x1, y1, x2, y2, hRS, hSR, hR, hS, hp, hq, hp1, hq1, hx, hy, hx', hy',
    e1, e2, e3⟩ := h
  exact ⟨R, S, p1, q1, y1, x1, y2, x2, hRS, hSR, hR, hS, hp, hq, hp1, hq1, hy, hx, hy', hx',
    higmanVCTauUnif_dleg_swap e1, higmanVCTauUnif_dleg_swap e2, higmanVCTauUnif_dleg_swap e3⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_hopCD_swap

end GroupApproximation.BooneHigman.Metabelian.Envelope
