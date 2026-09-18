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

/-- **A different first letter.** -/
theorem higmanVCTauFix3Vac_caseDiff {d : ℕ} (hd : 1 < d) {p q t' y' : List (Fin d)}
    {m0 m1 m2 e : Fin d} (r ys : List (Fin d)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hl : p.length = q.length) (hp3 : p.length ≤ 3) (hq3 : q.length ≤ 3)
    (htt : MapsCone (coneSwap p q hpq hqp) [m0, m1, m2] t') (ht' : t'.length ≤ 3)
    (hmy : MapsCone (coneSwap p q hpq hqp) (e :: ys) y') (hy' : y'.length = (e :: ys).length)
    (he : e ≠ m0)
    (hB : ¬ higmanVCTauFix3_BothFixed p q (m0 :: m1 :: m2 :: r) (e :: ys))
    (hF : ¬ higmanVCTauRest_OneFixed p q (m0 :: m1 :: m2 :: r) (e :: ys))
    (hF' : ¬ higmanVCTauRest_OneFixed q p (m0 :: m1 :: m2 :: r) (e :: ys)) :
    higmanVCTauComm_FlexA d p q (m0 :: m1 :: m2 :: r) (e :: ys) hpq hqp := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have ho := higmanVCTauSplit_other_ne hd
  have key : ∀ z0 z1 : Fin d, ¬ [z0, z1] <+: [m0, m1, m2] → ¬ [m0, m1, m2] <+: [z0, z1] →
      (¬ e :: ys <+: [z0, z1] ∧ ¬ [z0, z1] <+: e :: ys) →
      (([z0, z1] <+: p → [z0, z1] = p) ∧ ([z0, z1] <+: q → [z0, z1] = q)) →
      higmanVCTauComm_FlexA d p q (m0 :: m1 :: m2 :: r) (e :: ys) hpq hqp := by
    intro z0 z1 h1 h2 hyz hz
    obtain ⟨z', hzz, hz'⟩ := higmanVCTauFix3Vac_img hpq hqp hl hz.1 hz.2
    exact higmanVCTauFix3Vac_faA r hpq hqp h2 h1 (by simp) (by simp)
      (higmanVCTauBridge_inc_cons ys [m1, m2] he) hyz htt ht' hzz hz' hmy hy'
  have hz1 := higmanVCTauD2_inc2 (e := m0) [] [m2] (ho m1)
  by_cases hd1 : ([m0, higmanVCTau_other m1] <+: p → [m0, higmanVCTau_other m1] = p) ∧
      ([m0, higmanVCTau_other m1] <+: q → [m0, higmanVCTau_other m1] = q)
  · exact key m0 (higmanVCTau_other m1) hz1.1 hz1.2
      (higmanVCTauBridge_inc_cons ys [higmanVCTau_other m1] he) hd1
  have hW := higmanVCTauFix3Vac_notDef hp3 hq3 hd1
  rcases ys with _ | ⟨y1, ys⟩
  · exfalso
    rcases hW with ⟨c, hc⟩ | ⟨c, hc⟩
    · have hq3' : q.length = 3 := by
        have := congrArg List.length hc
        simp only [List.length_cons, List.length_nil] at this
        omega
      have hVy : ¬ [e] <+: q := fun h => by
        have := congrArg List.length (higmanVCTauConj_eq_of_prefix_right hpq hqp hmy h)
        simp only [List.length_cons, List.length_nil] at this
        omega
      rcases higmanVCTauFix3Vac_single hd r hc hq3' hVy he with h | h
      · exact hB h
      · exact hF' h
    · have hp3' : p.length = 3 := by
        have := congrArg List.length hc
        simp only [List.length_cons, List.length_nil] at this
        omega
      have hVy : ¬ [e] <+: p := fun h => by
        have := congrArg List.length (higmanVCTauConj_eq_of_prefix_left hpq hqp hmy h)
        simp only [List.length_cons, List.length_nil] at this
        omega
      rcases higmanVCTauFix3Vac_single hd r hc hp3' hVy he with h | h
      · exact hB (higmanVCTauFix3Vac_bfSwap h)
      · exact hF h
  have hi3 := higmanVCTauBridge_inc_cons [higmanVCTau_other y1] [m1, m2] he
  by_cases hd3 : ([e, higmanVCTau_other y1] <+: p → [e, higmanVCTau_other y1] = p) ∧
      ([e, higmanVCTau_other y1] <+: q → [e, higmanVCTau_other y1] = q)
  · exact key e (higmanVCTau_other y1) hi3.1 hi3.2 (higmanVCTauD2_inc2 ys [] (ho y1).symm) hd3
  exfalso
  rcases hW with ⟨c, hc⟩ | ⟨c, hc⟩ <;>
    rcases higmanVCTauFix3Vac_notDef hp3 hq3 hd3 with ⟨c', hc'⟩ | ⟨c', hc'⟩
  · exact he (List.cons.inj (hc.symm.trans hc')).1.symm
  · subst hc hc'
    exact hB (higmanVCTauFix3Vac_bf2 hd r ys he)
  · subst hc hc'
    exact hB (higmanVCTauFix3Vac_bfSwap (higmanVCTauFix3Vac_bf2 hd r ys he))
  · exact he (List.cons.inj (hc.symm.trans hc')).1.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_caseDiff

end GroupApproximation.BooneHigman.Metabelian.Envelope
