import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauClassifyCases
import GroupApproximation.Meta.AxiomGuard

/-!
# The classification is vacuous over `d ≥ 3` letters (lane bh-met-78a)

`higmanVCTauClassify_good`: over at least three letters, every equal-level instance of a
cone swap `(p, q)` with `|p|, |q| ≤ 3` that is not all short and whose source words are
incomparable has a flexible square (`FlexA` / `FlexB` on the source or on the target pair).
So the hypotheses of `HigmanVCTauUnifClassifyStatement` are contradictory for `d ≥ 3`, and
the statement reduces to its `d = 2` instance `HigmanVCTauClassifyTwoStatement`
(`higmanVCTauClassify_of_two`).

**Strength (LOUD): the residual is only EQUIVALENT to the target, not strictly weaker.**
`HigmanVCTauClassifyTwoStatement` is literally the `d = 2` specialization of
`HigmanVCTauUnifClassifyStatement`, so the target implies it trivially, and it implies the
target by `higmanVCTauClassify_of_two`.  The proof content removed is the whole `d ≥ 3` part
(every `d ≥ 3`, every `n`); what is left is the binary alphabet, where the `Shape` instances
genuinely occur.

**Truth check.**  The `d ≥ 3` case plan (the exact witnesses of `...Cone`, `...Fixed` and the
case split of `...Cases`) was checked by scratch `SP/bh-met-78a/plan.cpp` on every instance
with `d = 3`, words `≤ 4`: 13761576 instances, 0 failures.  The residual itself is the lane
bh-met-77y claim at `d = 2`, checked there for words `≤ 7` (every leftover is in `Shape`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Every instance over `d ≥ 3` letters has a flexible square.** -/
theorem higmanVCTauClassify_good {d : ℕ} (hd : 3 ≤ d) {p q x y x' y' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hn : x.length + y.length = x'.length + y'.length)
    (hs : ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3))
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) :
    higmanVCTauClassify_Good d p q x y x' y' hpq hqp := by
  have hd1 : 1 < d := by omega
  rcases higmanVCTauClassify_tri hd1 hmx with
    ⟨r, rfl, rfl⟩ | ⟨r, rfl, rfl⟩ | ⟨hxp, hxq, hx'⟩
  · have e1 : (p ++ r).length = p.length + r.length := List.length_append
    have e3 : (q ++ r).length = q.length + r.length := List.length_append
    rcases higmanVCTauClassify_tri hd1 hmy with
      ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩ | ⟨hyp, hyq, hy'⟩
    · -- `PP`
      have e2 : (p ++ t).length = p.length + t.length := List.length_append
      have e4 : (q ++ t).length = q.length + t.length := List.length_append
      exact higmanVCTauClassify_casePP hd hpq hqp hp hq (by omega)
        (fun h => hxy ((List.prefix_append_right_inj p).mpr h))
        (fun h => hyx ((List.prefix_append_right_inj p).mpr h))
    · -- `PQ`
      have e2 : (q ++ t).length = q.length + t.length := List.length_append
      have e4 : (p ++ t).length = p.length + t.length := List.length_append
      exact higmanVCTauClassify_casePQ hd hpq hqp hp hq (by omega)
    · -- `PF`
      rw [hy'] at hn hs ⊢
      exact higmanVCTauClassify_good_xy
        (higmanVCTauClassify_caseFP hd hpq hqp hp hq (by omega) hyp hyq (by omega))
  · have e1 : (q ++ r).length = q.length + r.length := List.length_append
    have e3 : (p ++ r).length = p.length + r.length := List.length_append
    rcases higmanVCTauClassify_tri hd1 hmy with
      ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩ | ⟨hyp, hyq, hy'⟩
    · -- `QP`
      have e2 : (p ++ t).length = p.length + t.length := List.length_append
      have e4 : (q ++ t).length = q.length + t.length := List.length_append
      exact higmanVCTauClassify_good_xy (higmanVCTauClassify_casePQ hd hpq hqp hp hq (by omega))
    · -- `QQ`
      have e2 : (q ++ t).length = q.length + t.length := List.length_append
      have e4 : (p ++ t).length = p.length + t.length := List.length_append
      exact higmanVCTauClassify_good_ab (higmanVCTauClassify_casePP hd hpq hqp hp hq (by omega)
        (fun h => hxy ((List.prefix_append_right_inj q).mpr h))
        (fun h => hyx ((List.prefix_append_right_inj q).mpr h)))
    · -- `QF`
      rw [hy'] at hn hs ⊢
      exact higmanVCTauClassify_good_ab (higmanVCTauClassify_good_xy
        (higmanVCTauClassify_caseFP hd hpq hqp hp hq (by omega) hyp hyq (by omega)))
  · rw [hx'] at hn hs ⊢
    rcases higmanVCTauClassify_tri hd1 hmy with
      ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩ | ⟨hyp, hyq, hy'⟩
    · -- `FP`
      have e2 : (p ++ t).length = p.length + t.length := List.length_append
      have e4 : (q ++ t).length = q.length + t.length := List.length_append
      exact higmanVCTauClassify_caseFP hd hpq hqp hp hq (by omega) hxp hxq (by omega)
    · -- `FQ`
      have e2 : (q ++ t).length = q.length + t.length := List.length_append
      have e4 : (p ++ t).length = p.length + t.length := List.length_append
      exact higmanVCTauClassify_good_ab
        (higmanVCTauClassify_caseFP hd hpq hqp hp hq (by omega) hxp hxq (by omega))
    · -- `FF`
      rw [hy'] at hn hs ⊢
      by_cases hx4 : 4 ≤ x.length
      · exact higmanVCTauClassify_caseFF hd hpq hqp hp hq hxp hxq hyp hyx hx4
      · exact higmanVCTauClassify_good_xy
          (higmanVCTauClassify_caseFF hd hpq hqp hp hq hyp hyq hxp hxy (by omega))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_good

/-- **Remaining gap (binary alphabet).**  `HigmanVCTauUnifClassifyStatement` at `d = 2`.
**EQUIVALENT** to the full statement (see `higmanVCTauClassify_of_two`); the `d ≥ 3` part is
discharged by `higmanVCTauClassify_good`. -/
def HigmanVCTauClassifyTwoStatement : Prop :=
  ∀ n : ℕ,
    ∀ (p q x y x' y' : List (Fin 2)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p),
      p.length ≤ 3 → q.length ≤ 3 →
      x.length + y.length = n → x'.length + y'.length = n →
      ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3) →
      ¬ higmanVCTauShort_OptionA 2 p q x y hpq hqp →
      ¬ higmanVCTauShort_OptionE 2 p q x y →
      ¬ higmanVCTauComm_OptionR 2 p q x y →
      ¬ higmanVCTauComm_FlexA 2 p q x y hpq hqp → ¬ higmanVCTauComm_FlexB 2 p q x y x' y' →
      ¬ higmanVCTauComm_FlexA 2 p q x' y' hpq hqp →
      ¬ higmanVCTauComm_FlexB 2 p q x' y' x y →
      ¬ higmanVCTauLevel_HopA 2 n p q x y x' y' hpq hqp →
      ¬ higmanVCTauLevel_HopA 2 n p q x' y' x y hpq hqp →
      ¬ higmanVCTauLevel_HopC 2 n p q x y x' y' →
      MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
      ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
      higmanVCTauUnif_Shape 2 p q x y ∨ higmanVCTauUnif_Shape 2 p q y x

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCTauClassifyTwoStatement

/-- **Reduction.**  The binary case gives the full classification: for `d ≥ 3` the
hypotheses are contradictory by `higmanVCTauClassify_good`. -/
theorem higmanVCTauClassify_of_two (h : HigmanVCTauClassifyTwoStatement) :
    HigmanVCTauUnifClassifyStatement := by
  intro d hd n p q x y x' y' hpq hqp hp hq hxn hxn' hs hOA hE hR hFA hFB hFA' hFB' hHA hHA'
    hHC hmx hmy hxy hyx hxy' hyx'
  by_cases h2 : d = 2
  · subst h2
    exact h n p q x y x' y' hpq hqp hp hq hxn hxn' hs hOA hE hR hFA hFB hFA' hFB' hHA hHA'
      hHC hmx hmy hxy hyx hxy' hyx'
  · exfalso
    rcases higmanVCTauClassify_good (by omega : 3 ≤ d) hpq hqp hp hq (by omega) hs hmx hmy
      hxy hyx with hG | hG | hG | hG
    · exact hFA hG
    · exact hFB hG
    · exact hFA' hG
    · exact hFB' hG

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_of_two

/-- **Wire.**  The deep residual from the binary classification. -/
theorem higmanVCTauClassify_deep_of_two (h : HigmanVCTauClassifyTwoStatement) :
    HigmanVCTauDeepResidualStatement :=
  higmanVCTauUnif_deep_of_classify (higmanVCTauClassify_of_two h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_deep_of_two

/-- **Wire.**  The `τ` half from the binary classification and the lower-level part. -/
theorem higmanVCTauClassify_tau_of_two (h : HigmanVCTauClassifyTwoStatement)
    (hLt : HigmanVCTauLevelLtStatement) : HigmanVCTauStatement :=
  higmanVCTauUnif_tau_of_classify (higmanVCTauClassify_of_two h) hLt

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_tau_of_two

end GroupApproximation.BooneHigman.Metabelian.Envelope
