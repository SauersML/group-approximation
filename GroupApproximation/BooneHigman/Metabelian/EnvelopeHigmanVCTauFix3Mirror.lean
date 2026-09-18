import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauFix3Flex
import GroupApproximation.Meta.AxiomGuard

/-!
# Form `sas` for the both-fixed family: long second word (lane bh-met-92l)

Both-fixed: `|p| = |q| = 3`, `x`, `y` incomparable with `p` and `q`.

* `higmanVCTauFix3_sasAR` (`|x| ≥ 2`, `y = t v` with `|t| = 3`, `x` incomparable with `t`):
  `a = (t, p)`, `c = (t, q)`, `A1 = (x, p v)`, `A2 = (x, q v)`.

All three sub-instances are at level `n` and known by flexible A (`higmanVCTauFix3_faR`)
through a length-2 word from `higmanVCTauFix3_exists_z`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Both fixed, `y = t v`, `x` incomparable with `t`.**  A form `sas` decomposition. -/
theorem higmanVCTauFix3_sasAR {d n : ℕ} (hd : 1 < d) {p q x t v : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length = 3) (hq : q.length = 3)
    (ht : t.length = 3) (hxp : ¬ x <+: p ∧ ¬ p <+: x) (hxq : ¬ x <+: q ∧ ¬ q <+: x)
    (hyp : ¬ p <+: t ++ v) (hyq : ¬ q <+: t ++ v) (hx2 : 2 ≤ x.length)
    (hxt : ¬ x <+: t ∧ ¬ t <+: x) (hn : x.length + (t ++ v).length = n) :
    higmanVCTauEqTwo_Sas d n p q x (t ++ v) x (t ++ v) hpq hqp := by
  have htp := higmanVCTauFix3_inc3 v (ht.trans hp.symm) hyp
  have htq := higmanVCTauFix3_inc3 v (ht.trans hq.symm) hyq
  have hft := higmanVCTauD2_fix hpq hqp htp htq
  have hxt' := higmanVCTauD2_fix htp.1 htp.2 hxt hxp
  have hxpq := higmanVCTauD2_fix hpq hqp hxp hxq
  have hxtq := higmanVCTauD2_fix htq.1 htq.2 hxt hxq
  have hn1 : x.length + (p ++ v).length = n := by
    simp only [List.length_append] at hn ⊢
    omega
  have hn2 : x.length + (q ++ v).length = n := by
    simp only [List.length_append] at hn ⊢
    omega
  obtain ⟨z1, hz1, hz1t, hz1p, hz1x⟩ :=
    higmanVCTauFix3_exists_z hd (u1 := t) (u2 := p) (u3 := x) (by omega) (by omega) hx2
  obtain ⟨z2, hz2, hz2p, hz2q, hz2x⟩ :=
    higmanVCTauFix3_exists_z hd (u1 := p) (u2 := q) (u3 := x) (by omega) (by omega) hx2
  obtain ⟨z3, hz3, hz3t, hz3q, hz3x⟩ :=
    higmanVCTauFix3_exists_z hd (u1 := t) (u2 := q) (u3 := x) (by omega) (by omega) hx2
  unfold higmanVCTauEqTwo_Sas
  refine ⟨t, p, t, q, x, p ++ v, x, q ++ v, htp.1, htp.2, htq.1, htq.2, by omega, by omega,
    by omega, by omega, hft, mapsCone_coneSwap_left hpq hqp, hxt',
    (mapsCone_coneSwap_left htp.1 htp.2).append v, hxpq,
    (mapsCone_coneSwap_left hpq hqp).append v, hxtq,
    (mapsCone_coneSwap_right htq.1 htq.2).append v, ?_, ?_, ?_⟩
  · exact higmanVCTauFix3_knownFA1 htp.1 htp.2 hn hn1
      (higmanVCTauFix3_faR v htp.1 htp.2 hz1t.2 hz1t.1 (by omega) (by omega) hxt
        ⟨hz1x.2, hz1x.1⟩ hz1t hz1p (mapsCone_coneSwap_left htp.1 htp.2) (by omega) hxt')
  · exact higmanVCTauFix3_knownFA1 hpq hqp hn1 hn2
      (higmanVCTauFix3_faR v hpq hqp hz2p.2 hz2p.1 (by omega) (by omega) hxp
        ⟨hz2x.2, hz2x.1⟩ hz2p hz2q (mapsCone_coneSwap_left hpq hqp) (by omega) hxpq)
  · exact higmanVCTauFix3_knownFA2 htq.1 htq.2 hn2 hn
      (higmanVCTauFix3_faR v htq.1 htq.2 hz3t.2 hz3t.1 (by omega) (by omega) hxt
        ⟨hz3x.2, hz3x.1⟩ hz3t hz3q (mapsCone_coneSwap_left htq.1 htq.2) (by omega) hxtq)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_sasAR

end GroupApproximation.BooneHigman.Metabelian.Envelope
