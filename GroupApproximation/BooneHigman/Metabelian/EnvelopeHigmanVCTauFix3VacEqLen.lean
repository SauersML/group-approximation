import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauFix3VacFam
import GroupApproximation.Meta.AxiomGuard

/-!
# The equal-length case of the vacuity (lane bh-met-92x)

For `|p| = |q|` and `x = m0 m1 m2 r`, flexible A holds at `(x, y)` off the both-fixed and
one-fixed families, through the cone swap `([m0, m1, m2] z)` for a length-2 word `z`:

* `higmanVCTauFix3Vac_caseSame`: `y = m0 ys`, with `z = [m0*, m0]` or `z = [m0*, m0*]`;
* `higmanVCTauFix3Vac_caseDiff`: `y = e ys`, `e ≠ m0`, with `z = [m0, m1*]` or
  `z = [e, y1*]` (`*` the other letter).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Same first letter.** -/
theorem higmanVCTauFix3Vac_caseSame {d : ℕ} (hd : 1 < d) {p q t' y' : List (Fin d)}
    {m0 m1 m2 : Fin d} (r ys : List (Fin d)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hl : p.length = q.length) (hp3 : p.length ≤ 3) (hq3 : q.length ≤ 3)
    (htt : MapsCone (coneSwap p q hpq hqp) [m0, m1, m2] t') (ht' : t'.length ≤ 3)
    (hmy : MapsCone (coneSwap p q hpq hqp) (m0 :: ys) y') (hy' : y'.length = (m0 :: ys).length)
    (hyx : ¬ m0 :: ys <+: m0 :: m1 :: m2 :: r)
    (hB : ¬ higmanVCTauFix3_BothFixed p q (m0 :: m1 :: m2 :: r) (m0 :: ys)) :
    higmanVCTauComm_FlexA d p q (m0 :: m1 :: m2 :: r) (m0 :: ys) hpq hqp := by
  have ho := higmanVCTauSplit_other_ne hd
  have key : ∀ z1 : Fin d, (([higmanVCTau_other m0, z1] <+: p → [higmanVCTau_other m0, z1] = p) ∧
      ([higmanVCTau_other m0, z1] <+: q → [higmanVCTau_other m0, z1] = q)) →
      higmanVCTauComm_FlexA d p q (m0 :: m1 :: m2 :: r) (m0 :: ys) hpq hqp := by
    intro z1 hz
    obtain ⟨z', hzz, hz'⟩ := higmanVCTauFix3Vac_img hpq hqp hl hz.1 hz.2
    have hinc := higmanVCTauBridge_inc_cons [z1] [m1, m2] (ho m0)
    by_cases hty : [m0, m1, m2] <+: m0 :: ys
    · obtain ⟨s, hs⟩ := hty
      rw [← hs]
      exact higmanVCTauFix3Vac_faB r s hpq hqp hinc.2 hinc.1 (by simp) (by simp) htt ht' hzz hz'
    · have hyt : ¬ m0 :: ys <+: [m0, m1, m2] :=
        fun h => hyx (h.trans (List.prefix_append [m0, m1, m2] r))
      exact higmanVCTauFix3Vac_faA r hpq hqp hinc.2 hinc.1 (by simp) (by simp) ⟨hyt, hty⟩
        (higmanVCTauBridge_inc_cons ys [z1] (ho m0).symm) htt ht' hzz hz' hmy hy'
  by_cases ha : ([higmanVCTau_other m0, m0] <+: p → [higmanVCTau_other m0, m0] = p) ∧
      ([higmanVCTau_other m0, m0] <+: q → [higmanVCTau_other m0, m0] = q)
  · exact key m0 ha
  by_cases hb : ([higmanVCTau_other m0, higmanVCTau_other m0] <+: p →
      [higmanVCTau_other m0, higmanVCTau_other m0] = p) ∧
      ([higmanVCTau_other m0, higmanVCTau_other m0] <+: q →
      [higmanVCTau_other m0, higmanVCTau_other m0] = q)
  · exact key (higmanVCTau_other m0) hb
  exfalso
  apply hB
  rcases higmanVCTauFix3Vac_notDef hp3 hq3 ha with ⟨c, hc⟩ | ⟨c, hc⟩ <;>
    rcases higmanVCTauFix3Vac_notDef hp3 hq3 hb with ⟨c', hc'⟩ | ⟨c', hc'⟩
  · exact absurd (List.cons.inj (List.cons.inj (hc.symm.trans hc')).2).1 (ho m0).symm
  · exact higmanVCTauFix3Vac_bfHead (m1 :: m2 :: r) ys hc hc' (ho m0).symm (ho m0).symm
  · exact higmanVCTauFix3Vac_bfHead (m1 :: m2 :: r) ys hc' hc (ho m0).symm (ho m0).symm
  · exact absurd (List.cons.inj (List.cons.inj (hc.symm.trans hc')).2).1 (ho m0).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_caseSame
