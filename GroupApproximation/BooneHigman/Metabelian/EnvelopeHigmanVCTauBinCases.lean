import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauBinFlex
import GroupApproximation.Meta.AxiomGuard

/-!
# The four position cases over the binary alphabet (lane bh-met-78b)

For a cone swap `s = (p, q)` over `Fin 2` with `|p|, |q| ≤ 3`, the position cases `PQ`, `PP`,
`FP` and `FF` have a flexible square (`higmanVCTauClassify_Good`) outside two families:
`PQ` with `|p| + |q| = 3` (excluded by hypothesis `hF` of `casePQ`) and `FF` with
`|p| = |q| = 3` (excluded by hypothesis `h2` of `caseFF`); in case `FP` the one leftover
configuration is exactly `higmanVCTauUnif_Shape`.  The squares are those of
`EnvelopeHigmanVCTauBinFlex` and `EnvelopeHigmanVCTauClassifyCone` / `...Fixed`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Case `PQ`** over `Fin 2`, away from `|p| + |q| = 3`. -/
theorem higmanVCTauBin_casePQ {p q r t : List (Fin 2)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hp : p.length ≤ 3) (hq : q.length ≤ 3) (hF : p.length + q.length ≠ 3)
    (hs : 3 ≤ (p ++ r).length ∨ 3 ≤ (q ++ t).length) :
    higmanVCTauClassify_Good 2 p q (p ++ r) (q ++ t) (q ++ r) (p ++ t) hpq hqp := by
  obtain ⟨a, p', rfl⟩ := List.exists_cons_of_ne_nil (higmanVCTauClassify_ne_nil hpq)
  obtain ⟨b, q', rfl⟩ := List.exists_cons_of_ne_nil (higmanVCTauClassify_ne_nil hqp)
  have ep : (a :: p').length = p'.length + 1 := rfl
  have eq0 : (b :: q').length = q'.length + 1 := rfl
  by_cases hab : a = b
  · have hq2 : 2 ≤ (b :: q').length := by
      rcases q' with _ | ⟨b1, q''⟩
      · exact (hqp (List.cons_prefix_cons.mpr ⟨hab.symm, List.nil_prefix⟩)).elim
      · have e : (b :: b1 :: q'').length = q''.length + 1 + 1 := rfl
        omega
    obtain ⟨c, hc⟩ := higmanVCTauBin_flip a
    exact Or.inr (Or.inl (higmanVCTauClassify_pq1 hpq hqp hp hq hq2
      (higmanVCTauUnif_inc_cons hc [] p')
      (higmanVCTauUnif_inc_cons (fun h => hc (h.trans hab.symm)) [] q')))
  by_cases hq3 : (b :: q').length = 3
  · obtain ⟨b1, b2, q'', rfl⟩ := higmanVCTauClassify_two (by omega : 2 ≤ q'.length)
    obtain ⟨b1', hb1⟩ := higmanVCTauBin_flip b1
    have e : [b, b1'].length = 2 := rfl
    exact Or.inr (Or.inl (higmanVCTauBin_pqB (C := [b, b1']) hpq hqp hp hq (by omega)
      (higmanVCTauUnif_inc_cons (Ne.symm hab) [b1'] p')
      (higmanVCTauClassify_inc_cons2 b (higmanVCTauUnif_inc_cons hb1 [] (b2 :: q'')))))
  by_cases hp3 : (a :: p').length = 3
  · obtain ⟨a1, a2, p'', rfl⟩ := higmanVCTauClassify_two (by omega : 2 ≤ p'.length)
    obtain ⟨a1', ha1⟩ := higmanVCTauBin_flip a1
    have e : [a, a1'].length = 2 := rfl
    exact Or.inr (Or.inl (higmanVCTauBin_pqC (C := [a, a1']) hpq hqp hp hq (by omega)
      (higmanVCTauClassify_inc_cons2 a (higmanVCTauUnif_inc_cons ha1 [] (a2 :: p'')))
      (higmanVCTauUnif_inc_cons hab [a1'] q')))
  have hk : (a :: p').length = (b :: q').length := by omega
  have e1 : (p' ++ r).length = p'.length + r.length := List.length_append
  have e2 : (q' ++ t).length = q'.length + t.length := List.length_append
  have hx : (a :: p') ++ r = a :: (p' ++ r) := List.cons_append
  have hy : (b :: q') ++ t = b :: (q' ++ t) := List.cons_append
  have ex : (a :: (p' ++ r)).length = (p' ++ r).length + 1 := rfl
  have ey : (b :: (q' ++ t)).length = (q' ++ t).length + 1 := rfl
  rw [hx, hy] at hs ⊢
  by_cases hx3 : 3 ≤ (a :: (p' ++ r)).length
  · obtain ⟨b0, c0, u, hu⟩ := higmanVCTauClassify_two (by omega : 2 ≤ (p' ++ r).length)
    obtain ⟨b0', hb0⟩ := higmanVCTauBin_flip b0
    rw [hu]
    exact Or.inl (higmanVCTauBin_lead hk (by omega) hb0 (Ne.symm hab) (by omega))
  · have hy3 : 2 ≤ (q' ++ t).length := by omega
    obtain ⟨b0, c0, u, hu⟩ := higmanVCTauClassify_two hy3
    obtain ⟨b0', hb0⟩ := higmanVCTauBin_flip b0
    rw [hu]
    exact Or.inl (higmanVCTauUnif_flexA_swap
      (higmanVCTauBin_lead hk (by omega) hb0 hab (by omega)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_casePQ

/-- **Case `PP`** over `Fin 2`. -/
theorem higmanVCTauBin_casePP {p q r t : List (Fin 2)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hp : p.length ≤ 3) (hq : q.length ≤ 3) (hk : p.length = q.length) (hrt : ¬ r <+: t)
    (htr : ¬ t <+: r) :
    higmanVCTauClassify_Good 2 p q (p ++ r) (p ++ t) (q ++ r) (q ++ t) hpq hqp := by
  obtain ⟨a, p', rfl⟩ := List.exists_cons_of_ne_nil (higmanVCTauClassify_ne_nil hpq)
  obtain ⟨b, q', rfl⟩ := List.exists_cons_of_ne_nil (higmanVCTauClassify_ne_nil hqp)
  have ep : (a :: p').length = p'.length + 1 := rfl
  by_cases hab : a = b
  · have hp2 : 2 ≤ (a :: p').length := by
      rcases p' with _ | ⟨a1, p''⟩
      · exact (hpq (List.cons_prefix_cons.mpr ⟨hab, List.nil_prefix⟩)).elim
      · have e : (a :: a1 :: p'').length = p''.length + 1 + 1 := rfl
        omega
    obtain ⟨c, hc⟩ := higmanVCTauBin_flip a
    exact Or.inl (higmanVCTauClassify_pp1 hpq hqp hp hq hp2
      (higmanVCTauUnif_inc_cons hc [] p')
      (higmanVCTauUnif_inc_cons (fun h => hc (h.trans hab.symm)) [] q'))
  by_cases hp3 : (a :: p').length = 3
  · obtain ⟨a1, a2, p'', rfl⟩ := higmanVCTauClassify_two (by omega : 2 ≤ p'.length)
    obtain ⟨a1', ha1⟩ := higmanVCTauBin_flip a1
    have e : [a, a1'].length = 2 := rfl
    exact Or.inl (higmanVCTauBin_ppB (C := [a, a1']) hpq hqp hp hq (by omega)
      (higmanVCTauClassify_inc_cons2 a (higmanVCTauUnif_inc_cons ha1 [] (a2 :: p'')))
      (higmanVCTauUnif_inc_cons hab [a1'] q'))
  rcases r with _ | ⟨r0, r'⟩
  · exact absurd List.nil_prefix hrt
  rcases t with _ | ⟨t0, t'⟩
  · exact absurd List.nil_prefix htr
  rw [higmanVCTauClassify_cons_eq (a :: p') r0 r', higmanVCTauClassify_cons_eq (a :: p') t0 t']
  rcases p' with _ | ⟨a1, p''⟩
  · exact Or.inl (higmanVCTauBin_ppC (P := b :: q') hk (by omega) hk.symm
      (higmanVCTauUnif_inc_cons (Ne.symm hab) q' []))
  · obtain ⟨a1', ha1⟩ := higmanVCTauBin_flip a1
    have e : [a, a1'].length = 2 := rfl
    have e' : (a :: a1 :: p'').length = p''.length + 1 + 1 := rfl
    exact Or.inl (higmanVCTauBin_ppC (P := [a, a1']) hk (by omega) (by omega)
      (higmanVCTauClassify_inc_cons2 a (higmanVCTauUnif_inc_cons ha1 [] p'')))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_casePP

/-- `FP` with `|p| = |q| = 3`: a square A through `(E, p)`, `|E| ≤ 2`, or `Shape`. -/
theorem higmanVCTauBin_fpL {p q x t : List (Fin 2)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hp3 : p.length = 3) (hk : p.length = q.length) (hxp : higmanVCTauUnif_Inc x p)
    (hxq : higmanVCTauUnif_Inc x q) (hs : 4 ≤ x.length ∨ 0 < t.length) :
    higmanVCTauComm_FlexA 2 p q x (p ++ t) hpq hqp ∨ higmanVCTauUnif_Shape 2 p q x (p ++ t) := by
  obtain ⟨a, p', rfl⟩ := List.exists_cons_of_ne_nil (higmanVCTauClassify_ne_nil hpq)
  obtain ⟨b, q', rfl⟩ := List.exists_cons_of_ne_nil (higmanVCTauClassify_ne_nil hqp)
  obtain ⟨e, x', rfl⟩ := List.exists_cons_of_ne_nil (higmanVCTauClassify_ne_nil hxp.1)
  have ep : (a :: p').length = p'.length + 1 := rfl
  have eq0 : (b :: q').length = q'.length + 1 := rfl
  obtain ⟨a1, a2, p'', rfl⟩ := higmanVCTauClassify_two (by omega : 2 ≤ p'.length)
  obtain ⟨b1, b2, q'', rfl⟩ := higmanVCTauClassify_two (by omega : 2 ≤ q'.length)
  have e3 : (a :: a1 :: a2 :: p'').length = p''.length + 1 + 1 + 1 := rfl
  have e3' : (b :: b1 :: b2 :: q'').length = q''.length + 1 + 1 + 1 := rfl
  have hp : (a :: a1 :: a2 :: p'').length ≤ 3 := hp3.le
  have hq : (b :: b1 :: b2 :: q'').length ≤ 3 := (hk.symm.trans hp3).le
  by_cases hea : e = a
  · by_cases hab : a = b
    · obtain ⟨e', he⟩ := higmanVCTauBin_flip e
      have l1 : [e'].length = 1 := rfl
      have hea' : e' ≠ a := fun h => he (h.trans hea.symm)
      have heb' : e' ≠ b := fun h => he (h.trans (hea.trans hab).symm)
      exact Or.inl (higmanVCTauBin_fpE (E := [e']) hpq hqp hp hq (by omega) hxp hxq
        (higmanVCTauUnif_inc_cons he [] x') (higmanVCTauUnif_inc_cons hea' [] (a1 :: a2 :: p''))
        (higmanVCTauUnif_inc_cons heb' [] (b1 :: b2 :: q'')))
    · obtain ⟨b1', hb1⟩ := higmanVCTauBin_flip b1
      have l2 : [b, b1'].length = 2 := rfl
      have hbe : b ≠ e := fun h => hab (hea.symm.trans h.symm)
      exact Or.inl (higmanVCTauBin_fpE (E := [b, b1']) hpq hqp hp hq (by omega) hxp hxq
        (higmanVCTauUnif_inc_cons hbe [b1'] x')
        (higmanVCTauUnif_inc_cons (Ne.symm hab) [b1'] (a1 :: a2 :: p''))
        (higmanVCTauClassify_inc_cons2 b (higmanVCTauUnif_inc_cons hb1 [] (b2 :: q''))))
  by_cases heb : e = b
  · have hab : a ≠ b := fun h => hea (heb.trans h.symm)
    obtain ⟨a1', ha1⟩ := higmanVCTauBin_flip a1
    have l2 : [a, a1'].length = 2 := rfl
    exact Or.inl (higmanVCTauBin_fpE (E := [a, a1']) hpq hqp hp hq (by omega) hxp hxq
      (higmanVCTauUnif_inc_cons (fun h => hea h.symm) [a1'] x')
      (higmanVCTauClassify_inc_cons2 a (higmanVCTauUnif_inc_cons ha1 [] (a2 :: p'')))
      (higmanVCTauUnif_inc_cons hab [a1'] (b1 :: b2 :: q'')))
  rcases x' with _ | ⟨x1, x''⟩
  · have hab : a = b := higmanVCTauBin_eq hea heb
    by_cases h11 : a1 = b1
    · obtain ⟨a1', ha1⟩ := higmanVCTauBin_flip a1
      have l2 : [a, a1'].length = 2 := rfl
      have H3 : higmanVCTauUnif_Inc [a, a1'] (b :: b1 :: b2 :: q'') := by
        rw [← hab, ← h11]
        exact higmanVCTauClassify_inc_cons2 a (higmanVCTauUnif_inc_cons ha1 [] (b2 :: q''))
      exact Or.inl (higmanVCTauBin_fpE (E := [a, a1']) hpq hqp hp hq (by omega) hxp hxq
        (higmanVCTauUnif_inc_cons (fun h => hea h.symm) [a1'] [])
        (higmanVCTauClassify_inc_cons2 a (higmanVCTauUnif_inc_cons ha1 [] (a2 :: p''))) H3)
    rcases t with _ | ⟨t0, t1⟩
    · have l0 : ([] : List (Fin 2)).length = 0 := rfl
      have l1 : [e].length = 1 := rfl
      omega
    obtain rfl : p'' = [] := List.eq_nil_of_length_eq_zero (by omega)
    obtain rfl : q'' = [] := List.eq_nil_of_length_eq_zero (by omega)
    have Hzz : higmanVCTauUnif_Inc [a, a1] [b, b1] := by
      rw [← hab]
      exact higmanVCTauClassify_inc_cons2 a (higmanVCTauUnif_inc_cons h11 [] [])
    exact Or.inr ⟨e, a2, b2, t0, [a, a1], [b, b1], t1, rfl, rfl, Hzz,
      higmanVCTauUnif_inc_cons hea [] [a1], higmanVCTauUnif_inc_cons heb [] [b1], rfl, rfl,
      Or.inl ⟨rfl, rfl⟩⟩
  · obtain ⟨x1', hx1⟩ := higmanVCTauBin_flip x1
    have l2 : [e, x1'].length = 2 := rfl
    exact Or.inl (higmanVCTauBin_fpE (E := [e, x1']) hpq hqp hp hq (by omega) hxp hxq
      (higmanVCTauClassify_inc_cons2 e (higmanVCTauUnif_inc_cons hx1 [] x''))
      (higmanVCTauUnif_inc_cons hea [x1'] (a1 :: a2 :: p''))
      (higmanVCTauUnif_inc_cons heb [x1'] (b1 :: b2 :: q'')))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_fpL

/-- `FP` with `t = []`, `|p| = |q| ≤ 2`, `|x| ≥ 4`. -/
theorem higmanVCTauBin_fpS {p q x : List (Fin 2)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hp : p.length ≤ 2) (hk : p.length = q.length) (hxp : higmanVCTauUnif_Inc x p)
    (hxq : higmanVCTauUnif_Inc x q) (hx : 4 ≤ x.length) :
    higmanVCTauClassify_Good 2 p q x p x q hpq hqp := by
  obtain ⟨e, x1, x', rfl⟩ := higmanVCTauClassify_two (by omega : 2 ≤ x.length)
  have ex : (e :: x1 :: x').length = x'.length + 1 + 1 := rfl
  have l0 : ([] : List (Fin 2)).length = 0 := rfl
  rcases x' with _ | ⟨x2, u⟩
  · omega
  obtain ⟨a, p', rfl⟩ := List.exists_cons_of_ne_nil (higmanVCTauClassify_ne_nil hpq)
  obtain ⟨b, q', rfl⟩ := List.exists_cons_of_ne_nil (higmanVCTauClassify_ne_nil hqp)
  obtain ⟨x1', hx1⟩ := higmanVCTauBin_flip x1
  by_cases hea : e = a
  · rcases p' with _ | ⟨a1, p''⟩
    · exact (hxp.2 (List.cons_prefix_cons.mpr ⟨hea.symm, List.nil_prefix⟩)).elim
    have ep : (a :: a1 :: p'').length = p''.length + 1 + 1 := rfl
    have eq0 : (b :: q').length = q'.length + 1 := rfl
    obtain rfl : p'' = [] := List.eq_nil_of_length_eq_zero (by omega)
    rcases q' with _ | ⟨b1, q''⟩
    · omega
    have eq1 : (b :: b1 :: q'').length = q''.length + 1 + 1 := rfl
    obtain rfl : q'' = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hxa : x1 ≠ a1 := fun h => hxp.2 (List.cons_prefix_cons.mpr ⟨hea.symm,
      List.cons_prefix_cons.mpr ⟨h.symm, List.nil_prefix⟩⟩)
    have hba : b ≠ a := by
      intro hba
      have hxb : x1 ≠ b1 := fun h => hxq.2 (List.cons_prefix_cons.mpr ⟨hba.trans hea.symm,
        List.cons_prefix_cons.mpr ⟨h.symm, List.nil_prefix⟩⟩)
      exact hpq (List.cons_prefix_cons.mpr ⟨hba.symm,
        List.cons_prefix_cons.mpr ⟨higmanVCTauBin_eq hxa hxb, List.nil_prefix⟩⟩)
    obtain ⟨b1', hb1⟩ := higmanVCTauBin_flip b1
    have hbe : b ≠ e := fun h => hba (h.trans hea)
    exact Or.inr (Or.inl (higmanVCTauClassify_fp3 (P := [e, x1, x2]) (u := u) (E := [b, b1'])
      (by omega) (by omega) hk rfl rfl hxp hxq
      (higmanVCTauUnif_inc_cons hba [b1'] [a1])
      (higmanVCTauClassify_inc_cons2 b (higmanVCTauUnif_inc_cons hb1 [] []))
      (higmanVCTauUnif_inc_cons hbe [b1'] [x1, x2])))
  · exact Or.inl (higmanVCTauBin_lead (b' := x1') hk hp hx1 (fun h => hea h.symm) le_rfl)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_fpS

/-- **Case `FP`** over `Fin 2`: a flexible square, or the leftover `Shape`. -/
theorem higmanVCTauBin_caseFP {p q x t : List (Fin 2)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hp : p.length ≤ 3) (hk : p.length = q.length) (hxp : higmanVCTauUnif_Inc x p)
    (hxq : higmanVCTauUnif_Inc x q) (hs : 4 ≤ x.length ∨ 0 < t.length) :
    higmanVCTauClassify_Good 2 p q x (p ++ t) x (q ++ t) hpq hqp ∨
      higmanVCTauUnif_Shape 2 p q x (p ++ t) := by
  by_cases hp3 : p.length = 3
  · rcases higmanVCTauBin_fpL hpq hqp hp3 hk hxp hxq hs with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  have hp2 : p.length ≤ 2 := by omega
  rcases t with _ | ⟨t0, t'⟩
  · simp only [List.append_nil]
    have l0 : ([] : List (Fin 2)).length = 0 := rfl
    exact Or.inl (higmanVCTauBin_fpS hpq hqp hp2 hk hxp hxq (by omega))
  · rw [higmanVCTauClassify_cons_eq p t0 t']
    exact Or.inl (Or.inl (higmanVCTauClassify_fp2 hpq hqp hp2 hk hxp hxq))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_caseFP

/-- **Case `FF`** over `Fin 2`, away from `|p| = |q| = 3`. -/
theorem higmanVCTauBin_caseFF {p q x y : List (Fin 2)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hp : p.length ≤ 3) (hq : q.length ≤ 3) (h2 : p.length ≤ 2 ∨ q.length ≤ 2)
    (hxp : higmanVCTauUnif_Inc x p) (hxq : higmanVCTauUnif_Inc x q)
    (hyp : higmanVCTauUnif_Inc y p) (hyq : higmanVCTauUnif_Inc y q) (hyx : ¬ y <+: x)
    (hx : 3 ≤ x.length) :
    higmanVCTauClassify_Good 2 p q x y x y hpq hqp := by
  obtain ⟨P, u, rfl, hP⟩ := higmanVCTauClassify_split hx
  by_cases hPy : P <+: y
  · obtain ⟨v, rfl⟩ := hPy
    rcases h2 with h2 | h2
    · exact Or.inr (Or.inl (higmanVCTauBin_ffC hpq hqp h2 hq hP hxp hxq))
    · exact Or.inr (Or.inl
        (higmanVCTauBin_flexB_pq (higmanVCTauBin_ffC hqp hpq h2 hp hP hxq hxp)))
  have hyP : higmanVCTauUnif_Inc y P := ⟨fun h => hyx (h.trans (List.prefix_append P u)), hPy⟩
  rcases h2 with h2 | h2
  · exact Or.inr (Or.inl (higmanVCTauClassify_ff3 hpq hqp h2 hq hP hxp hxq hyP hyp))
  · exact Or.inr (Or.inl (higmanVCTauBin_flexB_pq
      (higmanVCTauClassify_ff3 hqp hpq h2 hp hP hxq hxp hyP hyq)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_caseFF

end GroupApproximation.BooneHigman.Metabelian.Envelope
