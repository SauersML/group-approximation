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
      · exact absurd (List.cons_prefix_cons.mpr ⟨hab.symm, List.nil_prefix⟩) hqp
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

end GroupApproximation.BooneHigman.Metabelian.Envelope
