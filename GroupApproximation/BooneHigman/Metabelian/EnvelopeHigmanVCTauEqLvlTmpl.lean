import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauEqLvlLetters
import GroupApproximation.Meta.AxiomGuard

/-!
# Two explicit flexible squares (lane bh-met-77z)

* `higmanVCTauEqLvl_tmpl`: the pair `(P ++ R, o)` has the flexible-A shape for `σ` when
  `|P| = 3`, some word `Q` with `|Q| ≤ 2` is incomparable with `P` and `o`, `σ` carries `P` and
  `Q` to words of length `≤ 3` resp. `≤ 2`, and `σ` does not lengthen `o`.  The descent pair is
  `(P, Q)`, and the descended pair is `(Q ++ R, Q ++ r)` if `o = P ++ r`, else `(Q ++ R, o)`.
* `higmanVCTauEqLvl_t3`: at `(a ++ u, b ++ v) ↦ (b ++ u, a ++ v)` with `2 ≤ |a| ≤ 3` and
  `|b| ≤ 3`, flexible B holds through `(a, [e])` for a letter `e` avoiding the first letters
  of `a` and `b` (`d ≥ 3`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **The template square A.** -/
theorem higmanVCTauEqLvl_tmpl {d : ℕ} {σ : Equiv.Perm (Cantor (Fin d))}
    {P R o o' Q P' Q' : List (Fin d)} (hP3 : P.length = 3) (hoP : ¬ o <+: P)
    (hQ : Q.length ≤ 2) (hQP : ¬ Q <+: P) (hPQ : ¬ P <+: Q) (hQo : ¬ Q <+: o)
    (hoQ : ¬ o <+: Q) (hP' : MapsCone σ P P') (hP'l : P'.length ≤ 3)
    (hQ' : MapsCone σ Q Q') (hQ'l : Q'.length ≤ 2) (ho' : MapsCone σ o o')
    (ho'l : o'.length ≤ o.length) : higmanVCTauEqLvl_FA σ (P ++ R) o := by
  have hX : MapsCone (coneSwap P Q hPQ hQP) (Q ++ R) (P ++ R) :=
    (mapsCone_coneSwap_right hPQ hQP).append R
  by_cases hPo : P <+: o
  · obtain ⟨r, rfl⟩ := hPo
    refine ⟨P, Q, Q ++ R, Q ++ r, P', Q', Q' ++ R, Q' ++ r, hPQ, hQP, by omega, by omega, hX,
      (mapsCone_coneSwap_right hPQ hQP).append r, ?_, hP', hQ', hP'l, by omega,
      hQ'.append R, hQ'.append r, ?_⟩ <;>
    (simp only [List.length_append]; omega)
  · have ho : MapsCone (coneSwap P Q hPQ hQP) o o :=
      vgen_mapsCone_coneSwap_fix hPQ hQP hoP hPo hoQ hQo
    refine ⟨P, Q, Q ++ R, o, P', Q', Q' ++ R, o', hPQ, hQP, by omega, by omega, hX, ho, ?_,
      hP', hQ', hP'l, by omega, hQ'.append R, ho', ?_⟩ <;>
    (simp only [List.length_append]; omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_tmpl

/-- **The square B at a crossed pair.** -/
theorem higmanVCTauEqLvl_t3 {d : ℕ} (hd : 3 ≤ d) {a b : List (Fin d)} (u v : List (Fin d))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) (ha2 : 2 ≤ a.length) (ha3 : a.length ≤ 3)
    (hb3 : b.length ≤ 3) :
    higmanVCTauComm_FlexB d a b (a ++ u) (b ++ v) (b ++ u) (a ++ v) := by
  have ha0 : a ≠ [] := fun h => by
    subst h
    have h0 : ([] : List (Fin d)).length = 0 := rfl
    omega
  have hb0 : b ≠ [] := fun h => by
    subst h
    exact hba List.nil_prefix
  obtain ⟨a0, ha1, -⟩ := higmanVCTauEqLvl_head ha0
  obtain ⟨b0, hb1, hb2⟩ := higmanVCTauEqLvl_head hb0
  obtain ⟨e, hea, heb⟩ := higmanVCTauBridge_avoid2 hd a0 b0
  obtain ⟨h1, h2⟩ := ha1 e hea
  have hbv := higmanVCTauEqLvl_inc_append v hab hba
  have hbu := higmanVCTauEqLvl_inc_append u hab hba
  have fv := vgen_mapsCone_coneSwap_fix h2 h1 hbv.2 hbv.1 (hb2 e heb v).2 (hb2 e heb v).1
  have fu := vgen_mapsCone_coneSwap_fix h2 h1 hbu.2 hbu.1 (hb2 e heb u).2 (hb2 e heb u).1
  have fb := vgen_mapsCone_coneSwap_fix h2 h1 hba hab (hb1 e heb).2 (hb1 e heb).1
  refine ⟨a, [e], [e] ++ u, b ++ v, [e], b, b ++ u, [e] ++ v, h2, h1, ha3, by simp,
    (mapsCone_coneSwap_right h2 h1).append u, fv, ?_, mapsCone_coneSwap_left h2 h1, fb,
    by simp, hb3, fu, (mapsCone_coneSwap_left h2 h1).append v, ?_⟩ <;>
  (simp only [List.length_append, List.length_singleton]; omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauEqLvl_t3

end GroupApproximation.BooneHigman.Metabelian.Envelope
