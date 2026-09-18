import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauUnifComm
import GroupApproximation.Meta.AxiomGuard

/-!
# Uniform Hop D and Hop CD witnesses (lane bh-met-77y)

Fix a letter `a`, incomparable words `z`, `zo` of length two that do not start with `a`, and
`t = t0 t1` nonempty.  Let `A = (a, z c t)`.
* `higmanVCTauUnif_hopD`: for `{p0, q0} = {z, zo}`, Hop D (`higmanVCTauDeep_HopD`) holds for
  `s = (p0 c, q0 c)` and `A → B = (a, zo c t)`.  The parent leg `((p0, q0); A → B)` is easy by
  a flexible square A through `(z c, zo)`; every sibling `(p0 b, q0 b)`, `b ≠ c`, fixes `A`,
  and its leg is the commuting leg `higmanVCTauUnif_comm_leg` with `v = z c`, `w = zo`,
  `Qa = a t0'`.
* `higmanVCTauUnif_hopCD`: for `c ≠ c'`, Hop CD (`higmanVCTauDeep_HopCD`) holds for any
  `s = (p, q)` that `r = (z c, z c')` carries to `(p0 c', q0 c')`, and `A → B = (a, zo c' t)`,
  through `r`.  Its legs are: easy (a flexible square A through `(z c, zo)`); the Hop D above
  with letter `c'`; and the commuting leg with `v = zo c'`, `w = z`.

These are the uniform versions of the lane bh-met-77t scratch witnesses
`A = (0, 1000)`, `s = (100, 110)`, `w = (10, 11)` and `s = (100, 111)`, `r = (100, 101)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Uniform Hop D.** -/
theorem higmanVCTauUnif_hopD {d n : ℕ} (hd : 1 < d) {a c t0 : Fin d}
    {z zo t1 p0 q0 : List (Fin d)} (hz : z.length = 2) (hzo : zo.length = 2)
    (hzz : higmanVCTauUnif_Inc z zo) (haz : higmanVCTauUnif_Inc [a] z)
    (hazo : higmanVCTauUnif_Inc [a] zo) (hw : (z = p0 ∧ zo = q0) ∨ (z = q0 ∧ zo = p0))
    (hn : [a].length + (z ++ [c] ++ (t0 :: t1)).length = n) :
    higmanVCTauDeep_HopD d n (p0 ++ [c]) (q0 ++ [c]) [a] (z ++ [c] ++ (t0 :: t1)) [a]
      (zo ++ [c] ++ (t0 :: t1)) := by
  obtain ⟨h0, hp0a, hq0a, hp0, hq0⟩ := higmanVCTauUnif_pair hz hzo hzz haz hazo hw
  obtain ⟨hm1, hm2⟩ := higmanVCTauUnif_maps_pair h0.1 h0.2 hw
  have e1 := higmanVCTauUnif_len3 z c (t0 :: t1)
  have e2 := higmanVCTauUnif_len3 zo c (t0 :: t1)
  have e3 : (zo ++ (t0 :: t1)).length = zo.length + (t0 :: t1).length := List.length_append
  have e4 : (z ++ (t0 :: t1)).length = z.length + (t0 :: t1).length := List.length_append
  have e5 := higmanVCTauUnif_len1 z c
  have e6 := higmanVCTauUnif_len1 zo c
  have e7 : [a].length = 1 := rfl
  have hPQ := higmanVCTauUnif_incL [c] hzz
  have hFA : higmanVCTauComm_FlexA d p0 q0 [a] (z ++ [c] ++ (t0 :: t1)) h0.1 h0.2 :=
    ⟨z ++ [c], zo, [a], zo ++ (t0 :: t1), zo ++ [c], z, [a], z ++ (t0 :: t1), hPQ.1, hPQ.2,
      by omega, by omega,
      higmanVCTauUnif_fix hPQ.1 hPQ.2 (higmanVCTauUnif_incR [c] haz) hazo,
      (mapsCone_coneSwap_right hPQ.1 hPQ.2).append (t0 :: t1), by omega,
      hm1.append [c], hm2, by omega, by omega,
      higmanVCTauUnif_fix h0.1 h0.2 hp0a hq0a, hm2.append (t0 :: t1), by omega⟩
  refine ⟨p0, q0, c, h0.1, h0.2, rfl, rfl, higmanVCTauUnif_fix h0.1 h0.2 hp0a hq0a,
    (hm1.append [c]).append (t0 :: t1),
    Or.inl ⟨by omega, by omega, Or.inr (Or.inr (Or.inl ⟨h0.1, h0.2, hFA⟩))⟩, fun b hb => ?_⟩
  have hcb : c ≠ b := fun h => hb h.symm
  obtain ⟨hs1, hs2⟩ := higmanVCTauUnif_sib hcb hzz hw
  refine ⟨higmanVCTauUnif_fix _ _ (higmanVCTauUnif_incR [b] hp0a)
      (higmanVCTauUnif_incR [b] hq0a),
    higmanVCTauUnif_fix _ _ (higmanVCTauUnif_incL (t0 :: t1) hs1)
      (higmanVCTauUnif_incL (t0 :: t1) hs2), ?_⟩
  exact higmanVCTauUnif_comm_leg (w := zo) (Qa := [a] ++ [higmanVCTau_other t0]) (by omega)
    hzo (higmanVCTauUnif_len_qa _ _) (higmanVFP_len_succ hp0.le b)
    (higmanVFP_len_succ hq0.le b) hn (higmanVCTauUnif_incR [c] haz) hazo hPQ
    (higmanVCTauUnif_qaL c haz) (higmanVCTauUnif_qaT hd a t0 t1)
    (higmanVCTauUnif_incB [b] [b] h0) (higmanVCTauUnif_incS (higmanVCTauUnif_incR [b] hp0a))
    (higmanVCTauUnif_incS hs1) (higmanVCTauUnif_qaR b hp0a)
    (higmanVCTauUnif_incS (higmanVCTauUnif_incR [b] hq0a)) (higmanVCTauUnif_incS hs2)
    (higmanVCTauUnif_qaR b hq0a)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_hopD

/-- **Uniform Hop CD**, through `r = (z c, z c')`. -/
theorem higmanVCTauUnif_hopCD {d n : ℕ} (hd : 1 < d) {a c c' t0 : Fin d}
    {z zo t1 p q p0 q0 : List (Fin d)} (hz : z.length = 2) (hzo : zo.length = 2)
    (hzz : higmanVCTauUnif_Inc z zo) (haz : higmanVCTauUnif_Inc [a] z)
    (hazo : higmanVCTauUnif_Inc [a] zo) (hcc : c ≠ c')
    (hw : (z = p0 ∧ zo = q0) ∨ (z = q0 ∧ zo = p0))
    (hmp : MapsCone (coneSwap (z ++ [c]) (z ++ [c']) (higmanVFP_ne_letter z hcc)
      (higmanVFP_ne_letter z (Ne.symm hcc))) p (p0 ++ [c']))
    (hmq : MapsCone (coneSwap (z ++ [c]) (z ++ [c']) (higmanVFP_ne_letter z hcc)
      (higmanVFP_ne_letter z (Ne.symm hcc))) q (q0 ++ [c']))
    (hn : [a].length + (z ++ [c] ++ (t0 :: t1)).length = n) :
    higmanVCTauDeep_HopCD d n p q [a] (z ++ [c] ++ (t0 :: t1)) [a]
      (zo ++ [c'] ++ (t0 :: t1)) := by
  obtain ⟨_, _, _, hp0, hq0⟩ := higmanVCTauUnif_pair hz hzo hzz haz hazo hw
  have hR := higmanVCTauUnif_inc_letter z hcc
  have e1 := higmanVCTauUnif_len3 z c (t0 :: t1)
  have e2 := higmanVCTauUnif_len3 z c' (t0 :: t1)
  have e3 := higmanVCTauUnif_len3 zo c' (t0 :: t1)
  have e4 : (zo ++ (t0 :: t1)).length = zo.length + (t0 :: t1).length := List.length_append
  have e5 := higmanVCTauUnif_len1 z c
  have e6 := higmanVCTauUnif_len1 z c'
  have e7 := higmanVCTauUnif_len1 zo c'
  have e8 : [a].length = 1 := rfl
  have hzoz := higmanVCTauUnif_incS hzz
  have hRa := higmanVCTauUnif_incR [c] haz
  have hSa := higmanVCTauUnif_incR [c'] haz
  have hPQ := higmanVCTauUnif_incL [c] hzz
  have hFA : higmanVCTauComm_FlexA d (z ++ [c]) (z ++ [c']) [a] (z ++ [c] ++ (t0 :: t1))
      hR.1 hR.2 :=
    ⟨z ++ [c], zo, [a], zo ++ (t0 :: t1), z ++ [c'], zo, [a], zo ++ (t0 :: t1), hPQ.1, hPQ.2,
      by omega, by omega, higmanVCTauUnif_fix hPQ.1 hPQ.2 hRa hazo,
      (mapsCone_coneSwap_right hPQ.1 hPQ.2).append (t0 :: t1), by omega,
      mapsCone_coneSwap_left hR.1 hR.2,
      higmanVCTauUnif_fix hR.1 hR.2 (higmanVCTauUnif_incR [c] hzoz)
        (higmanVCTauUnif_incR [c'] hzoz), by omega, by omega,
      higmanVCTauUnif_fix hR.1 hR.2 hRa hSa,
      higmanVCTauUnif_fix hR.1 hR.2 (higmanVCTauUnif_incB (t0 :: t1) [c] hzoz)
        (higmanVCTauUnif_incB (t0 :: t1) [c'] hzoz), by omega⟩
  exact ⟨z ++ [c], z ++ [c'], p0 ++ [c'], q0 ++ [c'], [a], z ++ [c'] ++ (t0 :: t1), [a],
    zo ++ [c'] ++ (t0 :: t1), hR.1, hR.2, by omega, by omega, hmp, hmq,
    higmanVFP_len_succ hp0.le c', higmanVFP_len_succ hq0.le c',
    higmanVCTauUnif_fix hR.1 hR.2 hRa hSa,
    (mapsCone_coneSwap_left hR.1 hR.2).append (t0 :: t1),
    higmanVCTauUnif_fix hR.1 hR.2 hRa hSa,
    higmanVCTauUnif_fix hR.1 hR.2 (higmanVCTauUnif_incL (t0 :: t1)
        (higmanVCTauUnif_incB [c'] [c] hzoz))
      (higmanVCTauUnif_incL (t0 :: t1) (higmanVCTauUnif_incB [c'] [c'] hzoz)),
    Or.inl (Or.inl ⟨by omega, by omega, Or.inr (Or.inr (Or.inl ⟨hR.1, hR.2, hFA⟩))⟩),
    Or.inr (Or.inl (higmanVCTauUnif_hopD hd hz hzo hzz haz hazo hw (by omega))),
    Or.inl (higmanVCTauUnif_comm_leg (w := z) (Qa := [a] ++ [higmanVCTau_other t0])
      (by omega) hz (higmanVCTauUnif_len_qa _ _) (by omega) (by omega) (by omega)
      (higmanVCTauUnif_incR [c'] hazo) haz (higmanVCTauUnif_incL [c'] hzoz)
      (higmanVCTauUnif_qaL c' hazo) (higmanVCTauUnif_qaT hd a t0 t1) hR
      (higmanVCTauUnif_incS hRa) (higmanVCTauUnif_incB [c] [c'] hzz)
      (higmanVCTauUnif_qaR c haz) (higmanVCTauUnif_incS hSa)
      (higmanVCTauUnif_incB [c'] [c'] hzz) (higmanVCTauUnif_qaR c' haz))⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_hopCD

end GroupApproximation.BooneHigman.Metabelian.Envelope
