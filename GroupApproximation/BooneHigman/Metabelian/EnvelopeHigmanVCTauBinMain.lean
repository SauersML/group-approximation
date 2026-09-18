import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauBinCases
import GroupApproximation.Meta.AxiomGuard

/-!
# The binary classification outside the hop families (lane bh-met-78b)

`higmanVCTauBin_good`: over `Fin 2`, every equal-level instance of a cone swap `(p, q)` with
`|p|, |q| ≤ 3`, not all short, with incomparable source words, has a flexible square
(`higmanVCTauClassify_Good`) or is a `higmanVCTauUnif_Shape` instance, unless it lies in one
of the two *hop families* `higmanVCTauBin_Hop`:
* (F1) both source words lie in the cones of `p`, `q` and `|p| + |q| = 3`;
* (F2) both source words are fixed and `|p| = |q| = 3`.
So `HigmanVCTauClassifyTwoStatement` reduces to `HigmanVCTauBinHopStatement`, its restriction
to the hop families (`higmanVCTauBin_classifyTwo_of_hop`).

**Strength (LOUD): the residual is a proper special case, hence only EQUIVALENT as a
proposition, not strictly weaker.**  `HigmanVCTauBinHopStatement` is the target with the one
extra hypothesis `higmanVCTauBin_Hop p q x y`, so the target implies it trivially; with
`higmanVCTauBin_classifyTwo_of_hop` the two are logically equivalent (as is any true special
case).  The instances removed are all binary instances outside F1 ∪ F2 (every position case
`PP`, `QQ`, `PF`, `QF`, `FP`, `FQ`; `PQ` / `QP` with `|p| + |q| ≠ 3`; `FF` unless
`|p| = |q| = 3`).  On F1 ∪ F2 the witness plan has no flexible square; there the target's
contradiction has to come from `HopA` / `HopC`, which involve level-`n` `Easy` squares.
(F1 is stated generously: its `PQ` instances with `p`, `q` sharing a first letter are in
fact covered by `higmanVCTauBin_casePQ`, but are left in the residual.)

**Truth check.**  The witness plan of `EnvelopeHigmanVCTauBinFlex` / `...Cases` was checked by
scratch `SP/bh-met-78b/plan2.cpp` over `Fin 2`, words `≤ 7`: 0 failures outside F1 ∪ F2
(the `FP` leftover being exactly `Shape`).  The residual is the lane bh-met-77y claim
restricted to F1 ∪ F2, which bh-met-77y checked at `d = 2` for words `≤ 7`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The two hop families over `Fin 2`: (F1) `|p| + |q| = 3` with both source words in the
cones; (F2) `|p| = |q| = 3` with both source words fixed. -/
def higmanVCTauBin_Hop (p q x y : List (Fin 2)) : Prop :=
  (p.length + q.length = 3 ∧ (p <+: x ∨ q <+: x) ∧ (p <+: y ∨ q <+: y)) ∨
    (p.length = 3 ∧ q.length = 3 ∧ higmanVCTauUnif_Inc x p ∧ higmanVCTauUnif_Inc x q ∧
      higmanVCTauUnif_Inc y p ∧ higmanVCTauUnif_Inc y q)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_Hop

/-- **Every binary instance outside the hop families has a flexible square or is `Shape`.** -/
theorem higmanVCTauBin_good {p q x y x' y' : List (Fin 2)} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hn : x.length + y.length = x'.length + y'.length)
    (hs : ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3))
    (hH : ¬ higmanVCTauBin_Hop p q x y)
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) :
    higmanVCTauClassify_Good 2 p q x y x' y' hpq hqp ∨ higmanVCTauUnif_Shape 2 p q x y ∨
      higmanVCTauUnif_Shape 2 p q y x := by
  have hd1 : 1 < 2 := by omega
  have lp := higmanVCTauClassify_len_pos hpq
  have lq := higmanVCTauClassify_len_pos hqp
  rcases higmanVCTauClassify_tri hd1 hmx with
    ⟨r, rfl, rfl⟩ | ⟨r, rfl, rfl⟩ | ⟨hxp, hxq, hx'⟩
  · have e1 : (p ++ r).length = p.length + r.length := List.length_append
    have e3 : (q ++ r).length = q.length + r.length := List.length_append
    rcases higmanVCTauClassify_tri hd1 hmy with
      ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩ | ⟨hyp, hyq, hy'⟩
    · -- `PP`
      have e2 : (p ++ t).length = p.length + t.length := List.length_append
      have e4 : (q ++ t).length = q.length + t.length := List.length_append
      exact Or.inl (higmanVCTauBin_casePP hpq hqp hp hq (by omega)
        (fun h => hxy ((List.prefix_append_right_inj p).mpr h))
        (fun h => hyx ((List.prefix_append_right_inj p).mpr h)))
    · -- `PQ`
      have e2 : (q ++ t).length = q.length + t.length := List.length_append
      have e4 : (p ++ t).length = p.length + t.length := List.length_append
      exact Or.inl (higmanVCTauBin_casePQ hpq hqp hp hq
        (fun h3 => hH (Or.inl ⟨h3, Or.inl (List.prefix_append p r),
          Or.inr (List.prefix_append q t)⟩)) (by omega))
    · -- `PF`
      rw [hy'] at hn hs ⊢
      rcases higmanVCTauBin_caseFP hpq hqp hp (by omega) hyp hyq (by omega) with h | h
      · exact Or.inl (higmanVCTauClassify_good_xy h)
      · exact Or.inr (Or.inr h)
  · have e1 : (q ++ r).length = q.length + r.length := List.length_append
    have e3 : (p ++ r).length = p.length + r.length := List.length_append
    rcases higmanVCTauClassify_tri hd1 hmy with
      ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩ | ⟨hyp, hyq, hy'⟩
    · -- `QP`
      have e2 : (p ++ t).length = p.length + t.length := List.length_append
      have e4 : (q ++ t).length = q.length + t.length := List.length_append
      exact Or.inl (higmanVCTauClassify_good_xy (higmanVCTauBin_casePQ hpq hqp hp hq
        (fun h3 => hH (Or.inl ⟨h3, Or.inr (List.prefix_append q r),
          Or.inl (List.prefix_append p t)⟩)) (by omega)))
    · -- `QQ`
      have e2 : (q ++ t).length = q.length + t.length := List.length_append
      have e4 : (p ++ t).length = p.length + t.length := List.length_append
      exact Or.inl (higmanVCTauClassify_good_ab (higmanVCTauBin_casePP hpq hqp hp hq
        (by omega) (fun h => hxy ((List.prefix_append_right_inj q).mpr h))
        (fun h => hyx ((List.prefix_append_right_inj q).mpr h))))
    · -- `QF`
      rw [hy'] at hn hs ⊢
      rcases higmanVCTauBin_caseFP hpq hqp hp (by omega) hyp hyq (by omega) with h | h
      · exact Or.inl (higmanVCTauClassify_good_ab (higmanVCTauClassify_good_xy h))
      · exact Or.inr (Or.inr (higmanVCTauBin_shape_pq h))
  · rw [hx'] at hn hs ⊢
    rcases higmanVCTauClassify_tri hd1 hmy with
      ⟨t, rfl, rfl⟩ | ⟨t, rfl, rfl⟩ | ⟨hyp, hyq, hy'⟩
    · -- `FP`
      have e2 : (p ++ t).length = p.length + t.length := List.length_append
      have e4 : (q ++ t).length = q.length + t.length := List.length_append
      rcases higmanVCTauBin_caseFP hpq hqp hp (by omega) hxp hxq (by omega) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · -- `FQ`
      have e2 : (q ++ t).length = q.length + t.length := List.length_append
      have e4 : (p ++ t).length = p.length + t.length := List.length_append
      rcases higmanVCTauBin_caseFP hpq hqp hp (by omega) hxp hxq (by omega) with h | h
      · exact Or.inl (higmanVCTauClassify_good_ab h)
      · exact Or.inr (Or.inl (higmanVCTauBin_shape_pq h))
    · -- `FF`
      rw [hy'] at hn hs ⊢
      by_cases h33 : p.length = 3 ∧ q.length = 3
      · exact (hH (Or.inr ⟨h33.1, h33.2, hxp, hxq, hyp, hyq⟩)).elim
      have h2 : p.length ≤ 2 ∨ q.length ≤ 2 := by omega
      by_cases hx3 : 3 ≤ x.length
      · exact Or.inl (higmanVCTauBin_caseFF hpq hqp hp hq h2 hxp hxq hyp hyq hyx hx3)
      · exact Or.inl (higmanVCTauClassify_good_xy
          (higmanVCTauBin_caseFF hpq hqp hp hq h2 hyp hyq hxp hxq hxy (by omega)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_good

/-- **Remaining gap (hop families).**  `HigmanVCTauClassifyTwoStatement` restricted to the
hop families `higmanVCTauBin_Hop`.  **LOUD: EQUIVALENT to the target as a proposition** (a
proper special case, instance-wise; see `higmanVCTauBin_classifyTwo_of_hop`). -/
def HigmanVCTauBinHopStatement : Prop :=
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
      higmanVCTauBin_Hop p q x y →
      MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
      ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
      higmanVCTauUnif_Shape 2 p q x y ∨ higmanVCTauUnif_Shape 2 p q y x

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCTauBinHopStatement

/-- **Reduction.**  The binary classification from its hop-family restriction: outside the
hop families the flexible-square hypotheses are contradicted by `higmanVCTauBin_good`. -/
theorem higmanVCTauBin_classifyTwo_of_hop (h : HigmanVCTauBinHopStatement) :
    HigmanVCTauClassifyTwoStatement := by
  intro n p q x y x' y' hpq hqp hp hq hxn hxn' hs hOA hE hR hFA hFB hFA' hFB' hHA hHA'
    hHC hmx hmy hxy hyx hxy' hyx'
  by_cases hH : higmanVCTauBin_Hop p q x y
  · exact h n p q x y x' y' hpq hqp hp hq hxn hxn' hs hOA hE hR hFA hFB hFA' hFB' hHA hHA'
      hHC hH hmx hmy hxy hyx hxy' hyx'
  · rcases higmanVCTauBin_good hpq hqp hp hq (by omega) hs hH hmx hmy hxy hyx with
      (hG | hG | hG | hG) | hG | hG
    · exact (hFA hG).elim
    · exact (hFB hG).elim
    · exact (hFA' hG).elim
    · exact (hFB' hG).elim
    · exact Or.inl hG
    · exact Or.inr hG

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_classifyTwo_of_hop

/-- **Wire.**  The deep residual from the hop-family restriction. -/
theorem higmanVCTauBin_deep_of_hop (h : HigmanVCTauBinHopStatement) :
    HigmanVCTauDeepResidualStatement :=
  higmanVCTauClassify_deep_of_two (higmanVCTauBin_classifyTwo_of_hop h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_deep_of_hop

/-- **Wire.**  The `τ` half from the hop-family restriction and the lower-level part. -/
theorem higmanVCTauBin_tau_of_hop (h : HigmanVCTauBinHopStatement)
    (hLt : HigmanVCTauLevelLtStatement) : HigmanVCTauStatement :=
  higmanVCTauClassify_tau_of_two (higmanVCTauBin_classifyTwo_of_hop h) hLt

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_tau_of_hop

end GroupApproximation.BooneHigman.Metabelian.Envelope
