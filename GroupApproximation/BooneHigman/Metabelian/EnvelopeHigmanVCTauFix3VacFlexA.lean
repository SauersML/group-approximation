import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauFix3VacEqLen
import GroupApproximation.Meta.AxiomGuard

/-!
# Flexible A in the equal-length case (lane bh-met-92x)

For `|p| = |q| ≤ 3`, an instance with `x` or `y` longer than `3`, off the both-fixed and
one-fixed families, has flexible A at `(x, y)`.

* `higmanVCTauFix3Vac_bfSwapXY`, `higmanVCTauFix3Vac_ofSwapXY`: the both-fixed and one-fixed
  families are symmetric in `x ↔ y`;
* `higmanVCTauFix3Vac_caseA`: flexible A for `3 ≤ |x|`;
* `higmanVCTauFix3Vac_flexA`: flexible A from the hypotheses of the rest statement.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The both-fixed family is symmetric in `x ↔ y`. -/
theorem higmanVCTauFix3Vac_bfSwapXY {d : ℕ} {p q x y : List (Fin d)}
    (h : higmanVCTauFix3_BothFixed p q x y) : higmanVCTauFix3_BothFixed p q y x := by
  unfold higmanVCTauFix3_BothFixed at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2, h.2.2.1, h.2.2.2.1⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_bfSwapXY

/-- The one-fixed family is symmetric in `x ↔ y`. -/
theorem higmanVCTauFix3Vac_ofSwapXY {d : ℕ} {p q x y : List (Fin d)}
    (h : higmanVCTauRest_OneFixed p q x y) : higmanVCTauRest_OneFixed p q y x := by
  unfold higmanVCTauRest_OneFixed at h ⊢
  obtain ⟨α, β, β', γ, δ, ε, w, h1, h2, h3, h4, h5⟩ := h
  exact ⟨α, β, β', γ, δ, ε, w, h1, h2, h3, h4, h5.symm.imp And.symm And.symm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_ofSwapXY

/-- **Flexible A for `3 ≤ |x|`** (equal lengths). -/
theorem higmanVCTauFix3Vac_caseA {d : ℕ} (hd : 1 < d) {p q x y y' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hl : p.length = q.length) (hp3 : p.length ≤ 3)
    (hq3 : q.length ≤ 3) (hx : 3 ≤ x.length) (hyx : ¬ y <+: x)
    (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hB : ¬ higmanVCTauFix3_BothFixed p q x y) (hF : ¬ higmanVCTauRest_OneFixed p q x y)
    (hF' : ¬ higmanVCTauRest_OneFixed q p x y) :
    higmanVCTauComm_FlexA d p q x y hpq hqp := by
  rcases x with _ | ⟨m0, _ | ⟨m1, _ | ⟨m2, r⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  obtain ⟨t', htt, ht'⟩ := higmanVCTauFix3Vac_img (w := [m0, m1, m2]) hpq hqp hl
    (higmanVCTauFix3Vac_def_long (by simp only [List.length_cons, List.length_nil]; omega))
    (higmanVCTauFix3Vac_def_long (by simp only [List.length_cons, List.length_nil]; omega))
  have ht3 : t'.length ≤ 3 := by simp [ht']
  have hy' : y'.length = y.length := by
    rcases higmanVCTauBridge_len_cases hd hpq hqp hmy with h | h | h <;> omega
  rcases y with _ | ⟨e, ys⟩
  · exact absurd List.nil_prefix hyx
  by_cases he : e = m0
  · subst he
    exact higmanVCTauFix3Vac_caseSame hd r ys hpq hqp hl hp3 hq3 htt ht3 hmy hy' hyx hB
  · exact higmanVCTauFix3Vac_caseDiff hd r ys hpq hqp hl hp3 hq3 htt ht3 hmy hy' he hB hF hF'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_caseA

/-- **Flexible A in the equal-length case**, from the hypotheses of the rest statement. -/
theorem higmanVCTauFix3Vac_flexA {d : ℕ} (hd : 1 < d) {p q x y x' y' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hl : p.length = q.length) (hp3 : p.length ≤ 3)
    (hq3 : q.length ≤ 3)
    (hs : ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3))
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hB : ¬ higmanVCTauFix3_BothFixed p q x y) (hF : ¬ higmanVCTauRest_OneFixed p q x y)
    (hF' : ¬ higmanVCTauRest_OneFixed q p x y) :
    higmanVCTauComm_FlexA d p q x y hpq hqp := by
  have hx' : x'.length = x.length := by
    rcases higmanVCTauBridge_len_cases hd hpq hqp hmx with h | h | h <;> omega
  have hy' : y'.length = y.length := by
    rcases higmanVCTauBridge_len_cases hd hpq hqp hmy with h | h | h <;> omega
  by_cases hx : 3 ≤ x.length
  · exact higmanVCTauFix3Vac_caseA hd hpq hqp hl hp3 hq3 hx hyx hmy hB hF hF'
  · have hy : 3 ≤ y.length := by omega
    exact higmanVCTauFix3Vac_faSwap (higmanVCTauFix3Vac_caseA hd hpq hqp hl hp3 hq3 hy hxy hmx
      (fun h => hB (higmanVCTauFix3Vac_bfSwapXY h)) (fun h => hF (higmanVCTauFix3Vac_ofSwapXY h))
      (fun h => hF' (higmanVCTauFix3Vac_ofSwapXY h)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_flexA

end GroupApproximation.BooneHigman.Metabelian.Envelope
