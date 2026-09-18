import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauFix3Flex
import GroupApproximation.Meta.AxiomGuard

/-!
# Form `sas` for the both-fixed family: a one-letter word (lane bh-met-92l)

Both-fixed: `|p| = |q| = 3`, `x`, `y` incomparable with `p` and `q`.  With `t = [x0 x1 x2]`
(fixed by `(p q)`) and `w = w0 w'`:

* `higmanVCTauFix3_sasB` (`x = t w`, `y = [e]`, `e ≠ x0`): `a = c = (t, [e])`,
  `A1 = A2 = (e w, t)`;
* `higmanVCTauFix3_sasBR` (`x = [e]`, `y = t w`, `e ≠ y0`): the mirror.

The outer sub-instances are flexible B (`higmanVCTauRest_fbL1/fbR1`); the middle one is
flexible A (`higmanVCTauFix3_faR/faL` with `r = []`) through `z = [e g]`, `g ≠ w0`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Both fixed, `y = [e]`.**  A form `sas` decomposition. -/
theorem higmanVCTauFix3_sasB {d n : ℕ} (hd : 1 < d) {p q : List (Fin d)}
    {x0 x1 x2 w0 e : Fin d} (w' : List (Fin d)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hp : p.length = 3) (hq : q.length = 3) (he : e ≠ x0)
    (hyp : ¬ [e] <+: p ∧ ¬ p <+: [e]) (hyq : ¬ [e] <+: q ∧ ¬ q <+: [e])
    (hxp : ¬ p <+: x0 :: x1 :: x2 :: w0 :: w') (hxq : ¬ q <+: x0 :: x1 :: x2 :: w0 :: w')
    (hn : (x0 :: x1 :: x2 :: w0 :: w').length + [e].length = n) :
    higmanVCTauEqTwo_Sas d n p q (x0 :: x1 :: x2 :: w0 :: w') [e]
      (x0 :: x1 :: x2 :: w0 :: w') [e] hpq hqp := by
  have ho := higmanVCTauSplit_other_ne hd
  have hg : higmanVCTau_other w0 ≠ w0 := ho w0
  have hb : x1 ≠ higmanVCTau_other x1 := (ho x1).symm
  have hp0 : p ≠ [] := by
    rintro rfl
    simp at hp
  have hq0 : q ≠ [] := by
    rintro rfl
    simp at hq
  have htp := higmanVCTauFix3_inc3c (w0 :: w') hp hxp
  have htq := higmanVCTauFix3_inc3c (w0 :: w') hq hxq
  have ha := higmanVCTauBridge_inc_cons [] [x1, x2] he
  have hz := higmanVCTauBridge_inc_cons [higmanVCTau_other w0] [x1, x2] he
  have hwt := higmanVCTauBridge_inc_cons (w0 :: w') [x1, x2] he
  have hwz := higmanVCTauD2_inc2 (e := e) w' [] hg.symm
  have hft := higmanVCTauD2_fix hpq hqp htp htq
  have hfe := higmanVCTauD2_fix hpq hqp hyp hyq
  have hfw := higmanVCTauD2_fix hpq hqp (higmanVCTauFix3_incHead (w0 :: w') hp0 hyp.1)
    (higmanVCTauFix3_incHead (w0 :: w') hq0 hyq.1)
  have hn1 : (e :: w0 :: w').length + [x0, x1, x2].length = n := by
    simp only [List.length_cons, List.length_nil] at hn ⊢
    omega
  have k2 := higmanVCTauFix3_faR [] hpq hqp hz.2 hz.1 (by simp) (by simp) hwt hwz
    (higmanVCTauFix3_incHead [higmanVCTau_other w0] hp0 hyp.1)
    (higmanVCTauFix3_incHead [higmanVCTau_other w0] hq0 hyq.1) hft (by simp) hfw
  rw [List.append_nil] at k2
  unfold higmanVCTauEqTwo_Sas
  refine ⟨[x0, x1, x2], [e], [x0, x1, x2], [e], e :: w0 :: w', [x0, x1, x2], e :: w0 :: w',
    [x0, x1, x2], ha.2, ha.1, ha.2, ha.1, by simp, by simp, by simp, by simp, hft, hfe,
    (mapsCone_coneSwap_left ha.2 ha.1).append (w0 :: w'), mapsCone_coneSwap_right ha.2 ha.1,
    hfw, hft, (mapsCone_coneSwap_right ha.2 ha.1).append (w0 :: w'),
    mapsCone_coneSwap_left ha.2 ha.1, ?_, ?_, ?_⟩
  · exact higmanVCTauFix3_knownFB1 hn hn1 (higmanVCTauRest_fbL1 (w0 :: w') hb he)
  · exact higmanVCTauFix3_knownFA1 hpq hqp hn1 hn1 k2
  · exact higmanVCTauFix3_knownFB2 hn1 hn (higmanVCTauRest_fbL1 (w0 :: w') hb he)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_sasB

/-- **Both fixed, `x = [e]`.**  A form `sas` decomposition (the mirror). -/
theorem higmanVCTauFix3_sasBR {d n : ℕ} (hd : 1 < d) {p q : List (Fin d)}
    {y0 y1 y2 w0 e : Fin d} (w' : List (Fin d)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hp : p.length = 3) (hq : q.length = 3) (he : e ≠ y0)
    (hxp : ¬ [e] <+: p ∧ ¬ p <+: [e]) (hxq : ¬ [e] <+: q ∧ ¬ q <+: [e])
    (hyp : ¬ p <+: y0 :: y1 :: y2 :: w0 :: w') (hyq : ¬ q <+: y0 :: y1 :: y2 :: w0 :: w')
    (hn : [e].length + (y0 :: y1 :: y2 :: w0 :: w').length = n) :
    higmanVCTauEqTwo_Sas d n p q [e] (y0 :: y1 :: y2 :: w0 :: w') [e]
      (y0 :: y1 :: y2 :: w0 :: w') hpq hqp := by
  have ho := higmanVCTauSplit_other_ne hd
  have hg : higmanVCTau_other w0 ≠ w0 := ho w0
  have hb : y1 ≠ higmanVCTau_other y1 := (ho y1).symm
  have hp0 : p ≠ [] := by
    rintro rfl
    simp at hp
  have hq0 : q ≠ [] := by
    rintro rfl
    simp at hq
  have htp := higmanVCTauFix3_inc3c (w0 :: w') hp hyp
  have htq := higmanVCTauFix3_inc3c (w0 :: w') hq hyq
  have ha := higmanVCTauBridge_inc_cons [] [y1, y2] he
  have hz := higmanVCTauBridge_inc_cons [higmanVCTau_other w0] [y1, y2] he
  have hwt := higmanVCTauBridge_inc_cons (w0 :: w') [y1, y2] he
  have hwz := higmanVCTauD2_inc2 (e := e) w' [] hg.symm
  have hft := higmanVCTauD2_fix hpq hqp htp htq
  have hfe := higmanVCTauD2_fix hpq hqp hxp hxq
  have hfw := higmanVCTauD2_fix hpq hqp (higmanVCTauFix3_incHead (w0 :: w') hp0 hxp.1)
    (higmanVCTauFix3_incHead (w0 :: w') hq0 hxq.1)
  have hn1 : [y0, y1, y2].length + (e :: w0 :: w').length = n := by
    simp only [List.length_cons, List.length_nil] at hn ⊢
    omega
  have k2 := higmanVCTauFix3_faL [] hpq hqp hz.2 hz.1 (by simp) (by simp) hwt hwz
    (higmanVCTauFix3_incHead [higmanVCTau_other w0] hp0 hxp.1)
    (higmanVCTauFix3_incHead [higmanVCTau_other w0] hq0 hxq.1) hft (by simp) hfw
  rw [List.append_nil] at k2
  unfold higmanVCTauEqTwo_Sas
  refine ⟨[e], [y0, y1, y2], [e], [y0, y1, y2], [y0, y1, y2], e :: w0 :: w', [y0, y1, y2],
    e :: w0 :: w', ha.1, ha.2, ha.1, ha.2, by simp, by simp, by simp, by simp, hfe, hft,
    mapsCone_coneSwap_left ha.1 ha.2, (mapsCone_coneSwap_right ha.1 ha.2).append (w0 :: w'),
    hft, hfw, mapsCone_coneSwap_right ha.1 ha.2,
    (mapsCone_coneSwap_left ha.1 ha.2).append (w0 :: w'), ?_, ?_, ?_⟩
  · exact higmanVCTauFix3_knownFB1 hn hn1 (higmanVCTauRest_fbR1 (w0 :: w') hb he)
  · exact higmanVCTauFix3_knownFA1 hpq hqp hn1 hn1 k2
  · exact higmanVCTauFix3_knownFB2 hn1 hn (higmanVCTauRest_fbR1 (w0 :: w') hb he)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_sasBR

end GroupApproximation.BooneHigman.Metabelian.Envelope
