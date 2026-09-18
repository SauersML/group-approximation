import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauFix3Flex
import GroupApproximation.Meta.AxiomGuard

/-!
# Form `sas` for the both-fixed family: long heads (lane bh-met-92l)

Both-fixed: `|p| = |q| = 3`, `x`, `y` incomparable with `p` and `q`, so `(x', y') = (x, y)`.
With `t` a length-3 head (fixed by `(p q)`, as `t` is incomparable with `p` and `q`):

* `higmanVCTauFix3_sasA` (`x = t w`, `¬ t <+: y`, `|y| ≥ 2`): `a = (t, p)`, `c = (t, q)`,
  `A1 = (p w, y)`, `A2 = (q w, y)`;
* `higmanVCTauFix3_sasC` (`x = t w`, `y = t v`): `a = (t, p)`, `c = (t, q)`,
  `A1 = (p w, p v)`, `A2 = (q w, q v)`;
* `higmanVCTauFix3_sasA'` (`|x| ≥ 2`, `y = t v`, `x` incomparable with `t`): `a = (t, p)`,
  `c = (t, q)`, `A1 = (x, p v)`, `A2 = (x, q v)`.

All three sub-instances are at level `n` and known by flexible A
(`higmanVCTauFix3_faL/faR/faC`) through a length-2 word from `higmanVCTauFix3_exists_z`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Both fixed, `x = t w`, `¬ t <+: y`.**  A form `sas` decomposition. -/
theorem higmanVCTauFix3_sasA {d n : ℕ} (hd : 1 < d) {p q t w y : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length = 3) (hq : q.length = 3)
    (ht : t.length = 3) (hxp : ¬ p <+: t ++ w) (hxq : ¬ q <+: t ++ w)
    (hyp : ¬ y <+: p ∧ ¬ p <+: y) (hyq : ¬ y <+: q ∧ ¬ q <+: y) (hy2 : 2 ≤ y.length)
    (hty : ¬ t <+: y) (hyx : ¬ y <+: t ++ w) (hn : (t ++ w).length + y.length = n) :
    higmanVCTauEqTwo_Sas d n p q (t ++ w) y (t ++ w) y hpq hqp := by
  have htp := higmanVCTauFix3_inc3 w (ht.trans hp.symm) hxp
  have htq := higmanVCTauFix3_inc3 w (ht.trans hq.symm) hxq
  have hyt : ¬ y <+: t ∧ ¬ t <+: y := ⟨fun h => hyx (h.trans (List.prefix_append t w)), hty⟩
  have hft := higmanVCTauD2_fix hpq hqp htp htq
  have hn1 : (p ++ w).length + y.length = n := by
    simp only [List.length_append] at hn ⊢
    omega
  have hn2 : (q ++ w).length + y.length = n := by
    simp only [List.length_append] at hn ⊢
    omega
  obtain ⟨z1, hz1, hz1t, hz1p, hz1y⟩ :=
    higmanVCTauFix3_exists_z hd (u1 := t) (u2 := p) (u3 := y) (by omega) (by omega) hy2
  obtain ⟨z2, hz2, hz2p, hz2q, hz2y⟩ :=
    higmanVCTauFix3_exists_z hd (u1 := p) (u2 := q) (u3 := y) (by omega) (by omega) hy2
  obtain ⟨z3, hz3, hz3t, hz3q, hz3y⟩ :=
    higmanVCTauFix3_exists_z hd (u1 := t) (u2 := q) (u3 := y) (by omega) (by omega) hy2
  unfold higmanVCTauEqTwo_Sas
  refine ⟨t, p, t, q, p ++ w, y, q ++ w, y, htp.1, htp.2, htq.1, htq.2, by omega, by omega,
    by omega, by omega, hft, mapsCone_coneSwap_left hpq hqp,
    (mapsCone_coneSwap_left htp.1 htp.2).append w, higmanVCTauD2_fix htp.1 htp.2 hyt hyp,
    (mapsCone_coneSwap_left hpq hqp).append w, higmanVCTauD2_fix hpq hqp hyp hyq,
    (mapsCone_coneSwap_right htq.1 htq.2).append w, higmanVCTauD2_fix htq.1 htq.2 hyt hyq,
    ?_, ?_, ?_⟩
  · exact higmanVCTauFix3_knownFA1 htp.1 htp.2 hn hn1
      (higmanVCTauFix3_faL w htp.1 htp.2 hz1t.2 hz1t.1 (by omega) (by omega) hyt
        ⟨hz1y.2, hz1y.1⟩ hz1t hz1p (mapsCone_coneSwap_left htp.1 htp.2) (by omega)
        (higmanVCTauD2_fix htp.1 htp.2 hyt hyp))
  · exact higmanVCTauFix3_knownFA1 hpq hqp hn1 hn2
      (higmanVCTauFix3_faL w hpq hqp hz2p.2 hz2p.1 (by omega) (by omega) hyp
        ⟨hz2y.2, hz2y.1⟩ hz2p hz2q (mapsCone_coneSwap_left hpq hqp) (by omega)
        (higmanVCTauD2_fix hpq hqp hyp hyq))
  · exact higmanVCTauFix3_knownFA2 htq.1 htq.2 hn2 hn
      (higmanVCTauFix3_faL w htq.1 htq.2 hz3t.2 hz3t.1 (by omega) (by omega) hyt
        ⟨hz3y.2, hz3y.1⟩ hz3t hz3q (mapsCone_coneSwap_left htq.1 htq.2) (by omega)
        (higmanVCTauD2_fix htq.1 htq.2 hyt hyq))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_sasA

/-- **Both fixed, `x = t w`, `y = t v`.**  A form `sas` decomposition. -/
theorem higmanVCTauFix3_sasC {d n : ℕ} (hd : 1 < d) {p q t w v : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length = 3) (hq : q.length = 3)
    (ht : t.length = 3) (hxp : ¬ p <+: t ++ w) (hxq : ¬ q <+: t ++ w)
    (hn : (t ++ w).length + (t ++ v).length = n) :
    higmanVCTauEqTwo_Sas d n p q (t ++ w) (t ++ v) (t ++ w) (t ++ v) hpq hqp := by
  have htp := higmanVCTauFix3_inc3 w (ht.trans hp.symm) hxp
  have htq := higmanVCTauFix3_inc3 w (ht.trans hq.symm) hxq
  have hft := higmanVCTauD2_fix hpq hqp htp htq
  have hn1 : (p ++ w).length + (p ++ v).length = n := by
    simp only [List.length_append] at hn ⊢
    omega
  have hn2 : (q ++ w).length + (q ++ v).length = n := by
    simp only [List.length_append] at hn ⊢
    omega
  obtain ⟨z1, hz1, hz1t, hz1p, -⟩ :=
    higmanVCTauFix3_exists_z hd (u1 := t) (u2 := p) (u3 := t) (by omega) (by omega) (by omega)
  obtain ⟨z2, hz2, hz2p, hz2q, -⟩ :=
    higmanVCTauFix3_exists_z hd (u1 := p) (u2 := q) (u3 := p) (by omega) (by omega) (by omega)
  obtain ⟨z3, hz3, hz3t, hz3q, -⟩ :=
    higmanVCTauFix3_exists_z hd (u1 := t) (u2 := q) (u3 := t) (by omega) (by omega) (by omega)
  unfold higmanVCTauEqTwo_Sas
  refine ⟨t, p, t, q, p ++ w, p ++ v, q ++ w, q ++ v, htp.1, htp.2, htq.1, htq.2, by omega,
    by omega, by omega, by omega, hft, mapsCone_coneSwap_left hpq hqp,
    (mapsCone_coneSwap_left htp.1 htp.2).append w, (mapsCone_coneSwap_left htp.1 htp.2).append v,
    (mapsCone_coneSwap_left hpq hqp).append w, (mapsCone_coneSwap_left hpq hqp).append v,
    (mapsCone_coneSwap_right htq.1 htq.2).append w,
    (mapsCone_coneSwap_right htq.1 htq.2).append v, ?_, ?_, ?_⟩
  · exact higmanVCTauFix3_knownFA1 htp.1 htp.2 hn hn1
      (higmanVCTauFix3_faC w v htp.1 htp.2 hz1t.2 hz1t.1 (by omega) (by omega) hz1t hz1p
        (mapsCone_coneSwap_left htp.1 htp.2) (by omega))
  · exact higmanVCTauFix3_knownFA1 hpq hqp hn1 hn2
      (higmanVCTauFix3_faC w v hpq hqp hz2p.2 hz2p.1 (by omega) (by omega) hz2p hz2q
        (mapsCone_coneSwap_left hpq hqp) (by omega))
  · exact higmanVCTauFix3_knownFA2 htq.1 htq.2 hn2 hn
      (higmanVCTauFix3_faC w v htq.1 htq.2 hz3t.2 hz3t.1 (by omega) (by omega) hz3t hz3q
        (mapsCone_coneSwap_left htq.1 htq.2) (by omega))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_sasC

end GroupApproximation.BooneHigman.Metabelian.Envelope
